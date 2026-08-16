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

def stripArgsN? : (n : Nat) → Expr → Option Expr
  | n + 1, .app f _ => stripArgsN? n f
  | 0, e => some e
  | _, _ => none

def throwProofError (source target : Expr) : MetaM α :=
  throwError "internal staging error: cannot prove equality between{indentExpr source}\nand{indentExpr target}"

structure ForallEq where
  domainEq? : Option Expr
  domainEq : Expr
  codomainEq : Expr
  targetFamily : Expr
  forallEq? : Option Expr

namespace ProveEq

mutual

variable (interp hGen : Expr)

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
  let source ← whnf source
  let target ← whnf target
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

/-- Returns `(n, source.stripArgsN n ≍ target.stripArgsN n)`. -/
partial def proveAppFnHEq (source target : Expr) : MetaM (Nat × Expr) := do
  let sourceFn := source.getAppFn
  let sourceNumArgs := source.getAppNumArgs
  if sourceFn.isConstOf ``cast && sourceNumArgs ≥ 4 then
    let n := sourceNumArgs - 4
    let mkApp3 _ _ h sourceFn' := source.stripArgsN n | unreachable!
    let some targetFn' := stripArgsN? n target | throwProofError source target
    let heq' ← proveHEq sourceFn' targetFn'
    let heq ← mkHEqTrans (← mkAppM ``cast_heq #[h, sourceFn']) heq'
    return (n, heq)
  let targetFn := target.getAppFn
  let targetNumArgs := target.getAppNumArgs
  if targetFn.isConstOf ``cast && targetNumArgs ≥ 4 then
    let n := targetNumArgs - 4
    let mkApp3 _ _ h targetFn' := target.stripArgsN n | unreachable!
    let some sourceFn' := stripArgsN? n source | throwProofError source target
    let heq' ← proveHEq sourceFn' targetFn'
    let heq ← mkHEqTrans heq' (← mkHEqSymm (← mkAppM ``cast_heq #[h, targetFn']))
    return (n, heq)
  unless sourceNumArgs == targetNumArgs do
    throwProofError source target
  return (sourceNumArgs, ← proveHEq sourceFn targetFn)

/-- Given `fnHEq : source.stripArgsN n ≍ target.stripArgsN n`, returns `source ≍ target`. -/
partial def proveAppHEq (fnHEq : Expr) : Nat → (source target : Expr) → MetaM Expr
  | 0, _, _ =>
    pure fnHEq
  | n + 1, .app sourceFn sourceArg, .app targetFn targetArg => do
    let fnHEq ← proveAppHEq fnHEq n sourceFn targetFn
    let fnTypeEq ← mkAppM ``type_eq_of_heq #[fnHEq]
    let fnEq ← mkEqOfHEq (← mkHEqTrans (← mkAppM ``cast_heq #[fnTypeEq, sourceFn]) fnHEq)
    let sourceFnType ← inferType sourceFn
    let targetFnType ← inferType targetFn
    let { domainEq?, domainEq, codomainEq, targetFamily, .. } ←
      proveForallEq sourceFnType targetFnType
    let argEq ← proveEq (← maybeCast sourceArg domainEq?) targetArg
    mkAppM ``app_hcongr #[targetFamily, domainEq, codomainEq, fnEq, argEq]
  | _, _, _ =>
    throwError "internal staging error: bad arity"

partial def proveHEq? (source target : Expr) (retryWhnf := true) : MetaM (Option Expr) := do
  if ← isDefEq source target then
    return none
  let sourceType ← whnf (← inferType source)
  let targetType ← whnf (← inferType target)
  match sourceType, targetType with
  | mkApp2 (.const sourceTypeFn _) _ _, mkApp2 (.const targetTypeFn _) _ _ =>
    if sourceTypeFn == ``Code && targetTypeFn == ``Code then
      return ← mkAppM ``Code.heq_of_gen #[hGen, source, target]
  | .forallE _ sourceDomain _ _, .forallE _ targetDomain _ _ =>
    let eqDenType := mkEqDen interp
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
  | .app .., _ | _, .app .. =>
    let mut source := source
    let mut target := target
    let (n, fnHEq) ←
      try
        proveAppFnHEq source target
      catch _ =>
        source ← whnf source
        target ← whnf target
        proveAppFnHEq source target
    proveAppHEq fnHEq n source target
  | .proj .., _ | _, .proj .. =>
    proveHEq (← expandProjection source) (← expandProjection target)
  | .mdata .., _ | _, .mdata .. =>
    proveHEq source.consumeMData target.consumeMData
  | .letE .., _ | _, .letE .. =>
    proveHEq (expandLet source #[]) (expandLet target #[])
  | _, _ =>
    if retryWhnf then
      proveHEq? (← whnf source) (← whnf target) false
    else
      throwProofError source target

end

end ProveEq

public def proveEq? := ProveEq.proveEq?

end Thyme.Elab
