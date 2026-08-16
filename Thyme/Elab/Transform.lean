module

public import Lean.Elab.Term.TermElabM
import Lean.Meta.Eval
import Thyme.Code
import Thyme.Elab.Check
import Thyme.Elab.Common
import Thyme.Elab.TypedOpTransform
import Thyme.Elab.QuoteTemplate
import Thyme.Elab.ProveEq

namespace Thyme.Elab

open Lean Elab Meta
open Lean.Elab.Term hiding mkConst
open TypedOpTransform

/-- `#[xs[0], ..., xs[n]] : Array type` -/
def mkArrayLitOf (u : Level) (type : Expr) (xs : Array Expr) : Expr :=
  let nil := .app (mkConst ``List.nil [u]) type
  let cons := .app (mkConst ``List.cons [u]) type
  let list := xs.foldr (mkApp2 cons) nil
  mkApp2 (mkConst ``List.toArray [u]) type list

def throwInternalStagingError [Monad m] [MonadError m] : m α :=
  throwError "internal staging error"

def metaMExprType : Expr := .app (mkConst ``MetaM) (mkConst ``Expr)

/--
An alternating quote/splice tree. `body` contains one synthetic opaque
metavariable hole per child. `children` maps each child's original metavariable to
its tree. Those metavariables may hot occur directly in `body` as they may be
behind delayed assignments.
-/
structure StagingTree where
  body : Expr
  children : Std.HashMap.Raw MVarId StagingTree

abbrev Children := Std.HashMap.Raw MVarId StagingTree

structure PendingChild where
  mvarId : MVarId
  originalMVarId : MVarId
  fvars : Array Expr
  child : StagingTree

def StagingTree.unpack (tree : StagingTree) : MetaM (Expr × Array PendingChild) := do
  let { body, children } := tree
  let body ← instantiateMVars body
  let mvarIds := body.collectMVars {} |>.result
  unless mvarIds.size = children.size do
    throwInternalStagingError
  let holes ← mvarIds.mapM fun mvarId => do
    let (originalMVarId, fvars) ← match ← getDelayedMVarAssignment? mvarId with
      | some { mvarIdPending, fvars } => pure (mvarIdPending, fvars)
      | none => pure (mvarId, #[])
    if ← originalMVarId.isDelayedAssigned then
      throwError "unexpected delayed metavariable chain"
    let some child := children[originalMVarId]?
      | throwInternalStagingError
    return { mvarId, originalMVarId, fvars, child }
  return (body, holes)

mutual

partial def buildQuote (tree : StagingTree) (freshCaptures : Array Expr)
    (quoteCaptures : Array Expr) : TermElabM Expr := do
  let (body, spliceHoles) ← tree.unpack
  let exprType := mkConst ``Expr
  let spliceActions ← spliceHoles.mapM fun hole => do
    let captureNames ← hole.originalMVarId.withContext do
      hole.fvars.mapM (·.fvarId!.getUserName)
    withLocalDeclD `fresh (.app (mkConst ``Array [.zero]) exprType) fun fresh => do
      let spliceAction ←
        buildSplice hole.child (freshCaptures.push fresh) (quoteCaptures ++ hole.fvars)
      let spliceAction ← mkLambdaFVars #[fresh] spliceAction
      pure (mkApp2 (mkConst ``mkLambdaFreshFVars) (toExpr captureNames) spliceAction)
  let spliceActions := mkArrayLitOf .zero metaMExprType spliceActions
  let captures := freshCaptures.foldl
    (mkApp3 (.const ``Array.append [.zero]) exprType)
    (.app (.const ``Array.empty [.zero]) exprType)
  let template := body.abstract (quoteCaptures ++ spliceHoles.map (.mvar ·.mvarId))
  let instantiateTemplate ← registerQuoteTemplate template
  return mkApp2 instantiateTemplate captures spliceActions

partial def buildSplice (tree : StagingTree) (freshCaptures : Array Expr)
    (quoteCaptures : Array Expr) : TermElabM Expr := do
  let (body, quoteHoles) ← tree.unpack
  for hole in quoteHoles do
    let quote ← buildQuote hole.child freshCaptures quoteCaptures
    hole.originalMVarId.assign quote
  instantiateMVars body

end

inductive TransformState where
  | initial
  | code
  | quote (children : Children)
  | splice (children? : Option Children)
  deriving Inhabited

abbrev TransformM :=
  StateRefT TransformState (StateRefT TypeChangedFVarSet TermElabM)

instance : Inhabited (TransformM α) := ⟨throw default⟩

def swapTransformState (s : TransformState) : TransformM TransformState :=
  modifyGet (·, s)

def isGenContext : TransformM Bool := do
  return (← get) matches .splice (some _)

def enterCodeContext (k : TransformM α) : TransformM α := do
  let suspended ← swapTransformState .code
  if suspended matches .code | .quote _ then
    throwMultiLevelStagingError
  let result ← k
  set suspended
  return result

def enterQuoteContext (k : TransformM α) : TransformM (α × Children) := do
  let suspended ← swapTransformState (.quote {})
  if suspended matches .code | .quote _ then
    throwMultiLevelStagingError
  let result ← k
  let .quote children ← swapTransformState suspended
    | throwInternalStagingError
  return (result, children)

def enterSpliceContext (k : TransformM α) : TransformM α := do
  let suspended ← get
  let children? ← match suspended with
    | .initial | .quote _ => pure (some {})
    | .code => pure none
    | .splice _ => throwInternalStagingError
  let state : TransformState := .splice children?
  set state
  let result ← k
  let .splice _ ← swapTransformState suspended
    | throwInternalStagingError
  return result

def recordChild (type : Expr) (child : StagingTree) : TransformM Expr := do
  let hole ← mkFreshExprMVar (some type) .syntheticOpaque
  let ok ← modifyGetThe TransformState fun
    | .quote children =>
      (true, .quote (children.insert hole.mvarId! child))
    | .splice (some children) =>
      (true, .splice (some (children.insert hole.mvarId! child)))
    | s =>
      (false, s)
  unless ok do
    throwInternalStagingError
  return hole

namespace TransformM

mutual

variable (instStaged hGen : Expr)

partial def transform (dir : TypingDir) (expected : dir.Input) (e : Expr) :
    TransformM (dir.Result Expr) :=
  TypedOpTransform.transform getOpAppTransform coerce dir expected e

partial def coerce (e : Expr) (sourceType targetType : Closure) :
    TransformM Expr := do
  if ← isGenContext then
    maybeCast e (← proveEq? instStaged hGen
      sourceType.instantiate targetType.instantiate)
  else
    return e

partial def getOpAppTransform : Name → TypedOpTransform.OpAppTransform TransformM
  | name =>
    if name == ``Code then
      .transform transformCode
    else if name == ``Code.mk then
      .transform transformQuote
    else if name == ``Code.den' then
      .transform transformSplice
    else
      .default

partial def transformCode (dir : TypingDir) (_ : dir.Input)
    (fn : Expr) (args : Vector Expr 2) : TransformM (dir.Result Expr) := do
  let .const _ [u] := fn | unreachable!
  let sourceTypeDen := args[1]
  let typeDen ←
    if ← isGenContext then
      pure (mkErasedTypeDen u instStaged)
    else
      let typeDen ← enterCodeContext do
        transform .synth () sourceTypeDen
      pure typeDen.val
  return .mk (mkApp2 fn instStaged typeDen)
    (.ofUnchangedExpr (.sort (mkLevelMax' .one u)))

partial def transformQuoteTree (sourceDen : Expr) : TransformM StagingTree := do
  let .lam hDenName hDenType sourceBody hDenBI := sourceDen
    | throwInternalStagingError
  let (body, children) ← enterQuoteContext do
    let body ← withLocalDecl hDenName hDenBI hDenType fun hDen => do
      transform .synth () (sourceBody.instantiate1 hDen)
    return body.val
  return { body, children }

partial def transformQuote (dir : TypingDir) (expectedType? : dir.Input)
    (quoteFn : Expr) (args : Vector Expr 4) : TransformM (dir.Result Expr) := do
  let .const _ [u] := quoteFn | unreachable!
  let sourceDen := args[2]
  unless ← isGenContext do
    throwInternalStagingError
  let tree ← transformQuoteTree sourceDen
  let actionBody ← recordChild metaMExprType tree
  let action ← mkLambdaFVars #[hGen] actionBody
  let interp := mkStagedInterp instStaged
  let gen := mkApp2 (mkConst ``Codegen.mk) interp action
  let expectedTypeDen? ← expectedType?.toOption.mapM fun expectedType => do
    let expectedType ← whnf expectedType.instantiate
    let_expr Code _ expectedTypeDen := expectedType
      | throwInternalStagingError
    pure expectedTypeDen
  let typeDen := expectedTypeDen?.getD (mkErasedTypeDen u instStaged)
  let quote := mkApp4 (mkConst ``Code.ofGen [u]) instStaged typeDen gen hGen
  return .mk quote
    (.ofChangedExpr (mkCodeType u instStaged typeDen))

partial def transformSpliceTree (u : Level) (sourceBody : Expr) :
    TransformM StagingTree := do
  unless ← isGenContext do
    throwInternalStagingError
  let interp := mkStagedInterp instStaged
  let typeDen := mkErasedTypeDen u instStaged
  let bodyType := mkCodeType u instStaged typeDen
  let body ← transform .check (.ofChangedExpr bodyType) sourceBody
  let gen := mkApp3 (mkConst ``Code.gen [u]) instStaged typeDen body
  let body := mkApp3 (mkConst ``Codegen.run) interp gen hGen
  let .splice (some children) ← get | throwInternalStagingError
  return { body, children }

partial def transformSplice (dir : TypingDir) (expectedType? : dir.Input)
    (spliceFn : Expr) (args : Vector Expr 4) : TransformM (dir.Result Expr) := do
  let .const _ [u] := spliceFn | unreachable!
  let sourceTypeDen := args[1]
  let sourceBody := args[2]
  let hDen := args[3]
  let sourceType := .ofUnchangedExpr (← instantiateTypeDen sourceTypeDen hDen)
  match ← get with
  | .quote _ =>
    let tree ← enterSpliceContext do
      transformSpliceTree u sourceBody
    let holeType := expectedType?.toOption.getD sourceType
    let hole ← recordChild holeType.instantiate tree
    return .mk hole holeType
  | .code =>
    enterSpliceContext do
      let bodyType := mkCodeType u instStaged sourceTypeDen
      let body ← transform .check (.ofUnchangedExpr bodyType) sourceBody
      let e := mkApp4 spliceFn instStaged sourceTypeDen body hDen
      coeResult coerce expectedType? e sourceType
  | _ =>
    throwInternalStagingError

end

end TransformM

def runTransform (x : TransformM α) : TermElabM α := do
  let lctx ← instantiateLCtxMVars (← getLCtx)
  withLCtx' lctx <| withNewMCtxDepth <|
    (x.run' .initial).run' {}

unsafe def evalCodegenImpl (codegen : Expr) : MetaM Expr := do
  let codegen ← evalExpr (Codegen .gen)
    (.app (mkConst ``Codegen) (mkConst ``Interp.gen))
    codegen
  codegen.run rfl

@[implemented_by evalCodegenImpl]
opaque evalCodegen (codegen : Expr) : MetaM Expr

public def evaluateSplice (stage : Int) (instStaged splice : Expr) : TermElabM Expr := do
  checkStages splice instStaged.fvarId? (startStage := stage)
  let_expr fn@Code.den' _ _ sourceBody _ := splice | throwInternalStagingError
  let .const _ [u] := fn | unreachable!
  runTransform do
    let hGenName ← mkFreshUserName hGenName
    withLocalDeclD hGenName (mkEqGen instStaged) fun hGen => do
      enterSpliceContext do
        let tree ← .transformSpliceTree instStaged hGen u sourceBody
        let action ← buildSplice tree #[] #[]
        let action ← mkLambdaFVars #[hGen] action
        let interp := mkStagedInterp instStaged
        let codegen := mkApp2 (mkConst ``Codegen.mk) interp action
        let codegen := codegen.replaceFVars #[instStaged]
          #[mkStaged (mkConst ``Interp.gen)]
        evalCodegen codegen

public def compileQuote (stage : Int) (instStaged hGen quote : Expr) : TermElabM Expr := do
  checkStages quote (startStage := stage)
  let_expr Code.mk _ _ sourceDen _ := quote | throwInternalStagingError
  runTransform do
    let tree ← .transformQuoteTree instStaged hGen sourceDen
    buildQuote tree #[] #[]

end Thyme.Elab
