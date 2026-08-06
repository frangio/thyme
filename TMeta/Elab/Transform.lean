module

public import Lean.Elab.Term.TermElabM
import TMeta.Elab.Common
import TMeta.Elab.TypedOpTransform
import TMeta.Elab.Check
import TMeta.Elab.Lemmas
import Lean.Meta.Eval
import TMeta.Code
import TMeta.Elab.Runtime

namespace TMeta.Elab.Transform

open Lean Elab Meta
open Lean.Elab.Term hiding mkConst
open TMeta.Elab.Lemmas
open TypedOpTransform

unsafe def evalCodegenImpl (gen : Expr) : MetaM Expr := do
  let result ← evalExpr Codegen (mkConst ``Codegen) gen
  result.run

@[implemented_by evalCodegenImpl]
opaque evalCodegen (gen : Expr) : MetaM Expr

/-- `#[xs[0], ..., xs[n]] : Array type` -/
def mkArrayLitOf (type : Expr) (xs : Array Expr) : MetaM Expr := do
  let u ← getDecLevel type
  let nil := .app (mkConst ``List.nil [u]) type
  let cons := .app (mkConst ``List.cons [u]) type
  let list := xs.foldr (mkApp2 cons) nil
  return mkApp2 (mkConst ``List.toArray [u]) type list

def expandProjection (e : Expr) : MetaM Expr := do
  let .proj structName idx struct := e | return e
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "unknown structure '{structName}'"
  let some fieldName := info.fieldNames[idx]?
    | throwError "invalid projection index {idx} for structure '{structName}'"
  mkProjection struct fieldName

def maybeCast (a : Expr) (h? : Option Expr) : MetaM Expr :=
  if let some h := h? then
    mkAppM ``cast #[h, a]
  else
    pure a

structure QuoteState where
  spliceGens : Array Expr
  spliceHoles : Array MVarId
  deriving Inhabited

structure DenContext where
  index : Expr
  hGen? : Option Expr := none
  quote? : Option QuoteState := none
  isEscaped : Bool := false
  deriving Inhabited

structure GenContext where
  index : Expr
  hGen : Expr

abbrev TransformState := Option DenContext

abbrev TransformM := StateRefT TransformState (StateRefT TypeChangedFVarSet TermElabM)

instance : Inhabited (TransformM α) := ⟨throw default⟩

def throwInternalStagingError [Monad m] [MonadError m] : m α :=
  throwError "internal staging error"

def getGenContext? : TransformM (Option GenContext) := do
  match ← get with
  | some { index, hGen? := some hGen, isEscaped := true, .. } =>
    return some { index, hGen }
  | _ =>
    return none

def modifyGetDenContext (f : DenContext → TermElabM (α × DenContext)) : TransformM α := do
  let some context ← modifyGet fun context? => (context?, none)
    | throwInternalStagingError
  let (result, context) ← f context
  set (some context)
  return result

def getQuote : TransformM QuoteState := do
  match ← get with
  | some { quote? := some quote, isEscaped := false, .. } =>
    return quote
  | _ =>
    throwInternalStagingError

def modifyQuote (f : QuoteState → QuoteState) : TransformM Unit := do
  modifyGetDenContext fun context => do
    let { quote? := some quote, isEscaped := true, .. } := context
      | throwInternalStagingError
    return ((), { context with quote? := some (f quote) })

def withDenContext (context : DenContext) (k : TransformM α) : TransformM α := do
  let suspended? ← get
  if let some { isEscaped := false, .. } := suspended? then
    throwError "staging error: multi-level staging is not supported"
  set (some context)
  let result ← k
  set suspended?
  return result

def enterCodeContext (index : Expr) (k : TransformM α) : TransformM α :=
  withDenContext { index } k

def enterQuoteContext (index : Expr) (k : Expr → TransformM α) : TransformM α := do
  let hGenName ← mkFreshUserName hGenName
  withLocalDeclD hGenName (mkEqGen index) fun hGen =>
    let hGen? := some hGen
    let quote? := some ⟨#[], #[]⟩
    withDenContext { index, hGen?, quote? } <| k hGen

def escapeDenContext (k : Option Expr → TransformM α) : TransformM α := do
  let hGen? ← modifyGetDenContext fun context => do
    if context.isEscaped then
      throwInternalStagingError
    return (context.hGen?, { context with isEscaped := true })
  let result ← k hGen?
  modifyGetDenContext fun context =>
    return ((), { context with isEscaped := false })
  return result

namespace TransformM

mutual

variable (index hGen : Expr)

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

partial def proveHEq? (source target : Expr) : MetaM (Option Expr) := do
  if ← isDefEq source target then
    return none
  let sourceType ← whnf (← inferType source)
  let targetType ← whnf (← inferType target)
  match sourceType, targetType with
  | mkApp2 (.const ``Code _) _ _, mkApp2 (.const ``Code _) _ _ =>
    return ← mkAppM ``Code.heq_of_gen #[hGen, source, target]
  | .forallE _ sourceDomain _ _, .forallE _ targetDomain _ _ =>
    let denType := mkDenType index
    if ← isDefEq sourceDomain denType then
      if ← isDefEq targetDomain denType then
        return ← mkAppM ``Den.heq_of_gen #[hGen, source, target]
  | _, _ => pure ()
  match source, target with
  | .forallE name sourceDomain sourceBody _,
      .forallE _ targetDomain targetBody _ => do
    let domainEq? ← proveEq? sourceDomain targetDomain
    withLocalDeclD name sourceDomain fun arg => do
      let bodyEq ← proveEq
        (sourceBody.instantiate1 arg)
        (targetBody.instantiate1 (← maybeCast arg domainEq?))
      let bodyEq ← mkLambdaFVars #[arg] bodyEq
      let targetCodomain := .lam name targetDomain targetBody .default
      let domainEq ← domainEq?.getDM (mkEqRefl sourceDomain)
      let eq ← mkAppM ``pi_congr' #[targetCodomain, domainEq, bodyEq]
      return ← mkHEqOfEq eq
  | .lam name sourceDomain sourceBody _,
      .lam _ targetDomain targetBody _ =>
    let .forallE _ targetTypeDomain targetTypeBody _ := targetType
      | throwError "function expected"
    let domainEq? ← proveEq? sourceDomain targetDomain
    withLocalDeclD name sourceDomain fun arg => do
      let bodyHEq ← proveHEq
        (sourceBody.instantiate1 arg)
        (targetBody.instantiate1 (← maybeCast arg domainEq?))
      let bodyHEq ← mkLambdaFVars #[arg] bodyHEq
      let targetCodomain := .lam name targetTypeDomain targetTypeBody .default
      let domainEq ← domainEq?.getDM (mkEqRefl sourceDomain)
      return ← mkAppM ``hfunext
        #[targetCodomain, target, domainEq, bodyHEq]
  | mkApp4 (.const ``cast _) _ _ h source, target =>
    mkHEqTrans
      (← mkAppM ``cast_heq #[h, source])
      (← proveHEq source target)
  | source, mkApp4 (.const ``cast _) _ _ h target =>
    mkHEqTrans
      (← proveHEq source target)
      (← mkHEqSymm (← mkAppM ``cast_heq #[h, target]))
  | .app sourceFn sourceArg, .app targetFn targetArg => do
    let .forallE name sourceDomain sourceBody _ ← whnf (← inferType sourceFn)
      | throwError "function expected"
    let .forallE _ targetDomain targetBody _ ← whnf (← inferType targetFn)
      | throwError "function expected"
    let domainEq? ← proveEq? sourceDomain targetDomain
    withLocalDeclD name sourceDomain fun arg => do
      let bodyEq ← proveEq
        (sourceBody.instantiate1 arg)
        (targetBody.instantiate1 (← maybeCast arg domainEq?))
      let bodyEq ← mkLambdaFVars #[arg] bodyEq
      let targetCodomain := .lam name targetDomain targetBody .default
      let domainEq ← domainEq?.getDM (mkEqRefl sourceDomain)
      let fnTypeEq ← mkAppM ``pi_congr' #[targetCodomain, domainEq, bodyEq]
      let fnEq ← proveEq (← mkAppM ``cast #[fnTypeEq, sourceFn]) targetFn
      let argEq ← proveEq (← maybeCast sourceArg domainEq?) targetArg
      mkAppM ``app_hcongr #[targetCodomain, domainEq, bodyEq, fnEq, argEq]
  | .proj .., _ | _, .proj .. =>
    proveHEq (← expandProjection source) (← expandProjection target)
  | .mdata .., _ | _, .mdata .. =>
    proveHEq source.consumeMData target.consumeMData
  | .letE .., _ | _, .letE .. =>
    proveHEq (expandLet source #[]) (expandLet target #[])
  | _, _ =>
    throwError "failed to prove staging-induced heterogeneous equality between{indentExpr source}\nand{indentExpr target}"

end

mutual

partial def coerce (e : Expr) (sourceType targetType : Closure) :
    TransformM Expr := do
  if let some { index, hGen } ← getGenContext? then
    maybeCast e (← proveEq? index hGen
      sourceType.instantiate targetType.instantiate)
  else
    return e

partial def transform (dir : TypingDir) (expected : dir.Input) (e : Expr) :
    TransformM (dir.Result Expr) :=
  TypedOpTransform.transform getOpAppTransform coerce dir expected e

partial def getOpAppTransform : Name → TypedOpTransform.OpAppTransform TransformM
  | name =>
    if name == ``Code then
      .transform transformCode
    else if name == ``Code.mk then
      .transform transformQuote
    else if name == ``Code.den then
      .transform transformSplice
    else
      .default

partial def transformCode (dir : TypingDir) (expectedType? : dir.Input)
    (fn : Expr) (args : Vector Expr 2) : TransformM (dir.Result Expr) := do
  let .const _ [u] := fn | unreachable!
  let index := args[0]
  let sourceTypeDen := args[1]
  let typeDen ←
    if let some { hGen, .. } ← getGenContext? then
      pure (mkDenElimType u index hGen)
    else
      let typeDen ← enterCodeContext index do
        transform .synth () sourceTypeDen
      pure typeDen.val
  let e := mkApp2 fn index typeDen
  coeResultM coerce expectedType? e false (inferType e)

partial def withQuoteAction (index sourceDen : Expr)
    (k : (hGen action : Expr) → TransformM α) : TransformM α := do
  let .lam hDenName hDenType sourceBody hDenBI := sourceDen
    | throwInternalStagingError
  enterQuoteContext index fun hGen => do
    let body ← withLocalDecl hDenName hDenBI hDenType fun hDen => do
      transform .synth () (sourceBody.instantiate1 hDen)
    let { spliceGens, spliceHoles, .. } ← getQuote
    let template : QuoteTemplate := {
      mctx := ← getMCtx
      body := body.val
      spliceHoles
    }
    let declName := (← getDeclName?).getD .anonymous
    let templateIndex ← template.register declName
    let spliceGens ← spliceGens.mapM instantiateMVars
    let spliceGens ← mkArrayLitOf (mkConst ``Codegen) spliceGens
    let action := mkApp3 (mkConst ``instantiateQuoteTemplate)
      (toExpr declName) (toExpr templateIndex) spliceGens
    k hGen action

partial def transformQuote (dir : TypingDir) (expectedType? : dir.Input)
    (quoteFn : Expr) (args : Vector Expr 4) : TransformM (dir.Result Expr) := do
  let .const _ [u] := quoteFn | unreachable!
  let index := args[0]
  let sourceTypeDen := args[1]
  let sourceDen := args[2]
  let gen ← withQuoteAction index sourceDen fun hGen action => do
    mkLambdaFVars #[hGen] (.app (mkConst ``Codegen.mk) action)
  if let some { hGen, .. } ← getGenContext? then
    let typeDen ← if let some expectedType := expectedType?.toOption then
      let expectedType ← whnf expectedType.instantiate
      let_expr Code _ expectedTypeDen := expectedType
        | throwInternalStagingError
      pure expectedTypeDen
    else
      pure (mkDenElimType u index hGen)
    let den := mkApp3 (mkConst ``Den.elim [u]) index typeDen hGen
    let e := mkCode u index typeDen den gen
    return .mk e (.ofChangedExpr (mkCodeType u index typeDen))
  else
    let e := mkCode u index sourceTypeDen sourceDen gen
    return .mk e (.ofUnchangedExpr (mkCodeType u index sourceTypeDen))

partial def transformSplice (dir : TypingDir) (expectedType? : dir.Input)
    (spliceFn : Expr) (args : Vector Expr 4) : TransformM (dir.Result Expr) := do
  let .const _ [u] := spliceFn | unreachable!
  let index := args[0]
  let sourceTypeDen := args[1]
  let sourceBody := args[2]
  let hDen := args[3]
  let sourceType := .ofUnchangedExpr (← instantiateTypeDen sourceTypeDen hDen)
  escapeDenContext fun
    | some hGen => do
      let typeDen := mkDenElimType u index hGen
      let bodyType := mkCodeType u index typeDen
      let body ← transform .check (.ofChangedExpr bodyType) sourceBody
      let gen := mkApp4 (mkConst ``Code.gen [u]) index typeDen body hGen
      let holeType := expectedType?.toOption.getD sourceType
      let hole ← mkFreshExprMVar (some holeType.instantiate) .syntheticOpaque
      modifyQuote fun quote => { quote with
        spliceGens := quote.spliceGens.push gen
        spliceHoles := quote.spliceHoles.push hole.mvarId!
      }
      return .mk hole holeType
    | none => do
      let bodyType := mkCodeType u index sourceTypeDen
      let body ← transform .check (.ofUnchangedExpr bodyType) sourceBody
      let e := mkApp4 spliceFn index sourceTypeDen body hDen
      coeResult coerce expectedType? e sourceType

end

end TransformM

def run (x : TransformM α) : TermElabM α := do
  let lctx ← instantiateLCtxMVars (← getLCtx)
  let localInstances ← getLocalInstances
  withLCtx lctx localInstances <| withMCtx {} <|
    (x.run' none).run' {}

public def evaluateSplice (stage : Int) (index splice : Expr) : TermElabM Expr := do
  checkStages splice index.fvarId? (startStage := stage)
  let_expr fn@Code.den _ _ sourceBody _ := splice | throwInternalStagingError
  let .const _ [u] := fn | unreachable!
  run do
    let hGenName ← mkFreshUserName hGenName
    withLocalDeclD hGenName (mkEqGen index) fun hGen => do
      let context : DenContext := {
        index
        hGen? := some hGen
        isEscaped := true
      }
      set (some context)
      let elimType := mkDenElimType u index hGen
      let bodyType := mkCodeType u index elimType
      let body ← TransformM.transform .check (.ofChangedExpr bodyType) sourceBody
      let gen := mkApp4 (mkConst ``Code.gen [u]) index elimType body hGen
      let genIndex := mkConst ``Interpretation.gen
      let genIndexRefl := mkApp2 (mkConst ``Eq.refl [.one])
        (mkConst ``Interpretation) genIndex
      let gen := gen.replaceFVars #[index, hGen] #[genIndex, genIndexRefl]
      evalCodegen gen

public def compileQuote (stage : Int) (index quote : Expr) : TermElabM Expr := do
  checkStages quote (startStage := stage)
  let_expr Code.mk _ _ sourceDen _ := quote | throwInternalStagingError
  run <| TransformM.withQuoteAction index sourceDen fun hGen action => do
    mkLambdaFVars #[hGen] action

end TMeta.Elab.Transform
