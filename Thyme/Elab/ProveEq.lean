module

public import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.WHNF
import Thyme.Code
import Thyme.Elab.Common
import Thyme.Elab.Lemmas

open Lean Elab Meta

namespace Thyme.Elab

public def maybeCast (a : Expr) (eq? : Option Expr) : MetaM Expr :=
  if let some eq := eq? then
    mkAppM ``cast #[eq, a]
  else
    pure a

def expandProjection (e : Expr) : MetaM Expr := do
  let .proj structName idx struct := e | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "unknown structure '{structName}'"
  let some fieldName := info.fieldNames[idx]?
    | throwError "invalid projection index {idx} for structure '{structName}'"
  mkProjection struct fieldName

structure ForallEq where
  domainEq? : Option Expr
  domainEq : Expr
  codomainEq : Expr
  targetFamily : Expr
  forallEq? : Option Expr

namespace ProveEq

mutual

variable (staged hGen : Expr)

/-- Returns a proof that a source expression equals its generative staging
translation. -/
partial def proveEq (source target : Expr) : MetaM Expr := do
  (← proveEq? source target).getDM (mkEqRefl source)

partial def proveEq? (source target : Expr) : MetaM (Option Expr) := do
  (← proveHEq? source target).mapM mkEqOfHEq

/-- Returns a proof that a source expression is heterogeneously equal to its
generative staging translation. -/
partial def proveHEq (source target : Expr) : MetaM Expr := do
  (← proveHEq? source target).getDM (mkHEqRefl source)

partial def proveForallEq (source target : Expr) : MetaM ForallEq := do
  match source, target with
  | .forallE name sourceDomain sourceCodomain _,
      .forallE _ targetDomain targetCodomain _ =>
    let domainEq? ← proveEq? sourceDomain targetDomain
    let domainEq ← domainEq?.getDM (mkEqRefl sourceDomain)
    let (codomainEq, codomainIsDefEq) ← withLocalDeclD name sourceDomain fun arg => do
        let codomainEq? ← proveEq?
          (sourceCodomain.instantiate1 arg)
          (targetCodomain.instantiate1 (← maybeCast arg domainEq?))
        let codomainEq ← codomainEq?.getDM (mkEqRefl (sourceCodomain.instantiate1 arg))
        return (← mkLambdaFVars #[arg] codomainEq, codomainEq?.isNone)
    let targetFamily := .lam name targetDomain targetCodomain .default
    let forallEq? ←
      if domainEq?.isNone && codomainIsDefEq then
        pure none
      else
        some <$> mkAppM ``pi_congr' #[targetFamily, domainEq, codomainEq]
    return { domainEq?, domainEq, codomainEq, targetFamily, forallEq? }
  | _, _ =>
    throwError "function expected"

partial def proveHEq? (source target : Expr) : MetaM (Option Expr) := do
  if ← isDefEq source target then
    return none
  let sourceType ← whnf (← inferType source)
  let targetType ← whnf (← inferType target)
  match sourceType, targetType with
  | mkApp2 (.const ``Code _) _ _, mkApp2 (.const ``Code _) _ _ =>
    return ← mkAppM ``Code.heq_of_gen #[hGen, source, target]
  | .forallE _ sourceDomain _ _, .forallE _ targetDomain _ _ =>
    let eqDenType := mkEqDen staged
    if ← isDefEq sourceDomain eqDenType then
      if ← isDefEq targetDomain eqDenType then
        return ← mkAppM ``Code.den_heq_of_gen #[hGen, source, target]
  | _, _ => pure ()
  match source, target with
  | source@(.forallE ..), target@(.forallE ..) => do
    let { forallEq?, .. } ← proveForallEq source target
    mkHEqOfEq <| ← forallEq?.getDM (mkEqRefl source)
  | .lam name sourceDomain sourceBody _,
      .lam _ targetDomain targetBody _ =>
    let .forallE _ _ targetCodomain _ := targetType
      | throwError "function expected"
    let domainEq? ← proveEq? sourceDomain targetDomain
    let bodyHEq ← withLocalDeclD name sourceDomain fun arg => do
      mkLambdaFVars #[arg] <| ← proveHEq
        (sourceBody.instantiate1 arg)
        (targetBody.instantiate1 (← maybeCast arg domainEq?))
    let domainEq ← domainEq?.getDM (mkEqRefl sourceDomain)
    let targetFamily := .lam name targetDomain targetCodomain .default
    mkAppM ``hfunext #[targetFamily, target, domainEq, bodyHEq]
  | mkApp4 (.const ``cast _) _ _ h source, target =>
    mkHEqTrans
      (← mkAppM ``cast_heq #[h, source])
      (← proveHEq source target)
  | source, mkApp4 (.const ``cast _) _ _ h target =>
    mkHEqTrans
      (← proveHEq source target)
      (← mkHEqSymm (← mkAppM ``cast_heq #[h, target]))
  | .app sourceFn sourceArg, .app targetFn targetArg => do
    let sourceFnType ← whnf (← inferType sourceFn)
    let targetFnType ← whnf (← inferType targetFn)
    let { domainEq?, domainEq, codomainEq, targetFamily, forallEq? } ←
      proveForallEq sourceFnType targetFnType
    let fnEq ← proveEq (← maybeCast sourceFn forallEq?) targetFn
    let argEq ← proveEq (← maybeCast sourceArg domainEq?) targetArg
    mkAppM ``app_hcongr #[targetFamily, domainEq, codomainEq, fnEq, argEq]
  | .proj .., _ | _, .proj .. =>
    proveHEq (← expandProjection source) (← expandProjection target)
  | .mdata .., _ | _, .mdata .. =>
    proveHEq source.consumeMData target.consumeMData
  | .letE .., _ | _, .letE .. =>
    proveHEq (expandLet source #[]) (expandLet target #[])
  | _, _ =>
    throwError "failed to prove staging-induced heterogeneous equality between{indentExpr source}\nand{indentExpr target}"

end

end ProveEq

public def proveEq? := ProveEq.proveEq?

end Thyme.Elab
