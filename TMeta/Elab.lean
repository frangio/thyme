module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import TMeta.Elab.Context
public meta import TMeta.Elab.Common
public meta import TMeta.Elab.Check
public meta import TMeta.Elab.Runtime
public meta import TMeta.Elab.Transform
public import TMeta.Code
public import TMeta.Elab.Check
public import TMeta.Elab.Transform
public import TMeta.Elab.Runtime
public import TMeta.Elab.Lemmas

open Lean Meta

namespace TMeta.Elab

public inductive PendingCodeCheck
    (stage : Int)
    (index : Interpretation)
    (typeDen : [Den index] → Sort u) : Prop where
  | done : PendingCodeCheck stage index typeDen

public abbrev PendingQuoteAction
    (_stage : Int)
    (index : Interpretation)
    (typeDen : [Den index] → Sort u)
    (_den : [Den index] → typeDen) : Type :=
  index = .gen → MetaM Expr

meta section

open Lean Elab Meta
open Lean.Elab.Term hiding mkConst

public register_option tmeta.checkCoherence : Bool := {
  defValue := false
  descr := "check that generated code is definitionally equal to its denotation"
}

def checkCoherence : Lean.Option Bool where
  name := `tmeta.checkCoherence
  defValue := false

def isDen (index : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq index (mkConst ``Interpretation.den)

def ensureNoMVars (e : Expr) : TermElabM Unit := do
  if e.hasMVar then
    tryPostpone
    let mvars ← getMVars e
    if ← logUnassignedUsingErrorInfos mvars then
      throwAbortTerm
    let levelMVars := (collectLevelMVars {} e).result
    if ← logUnassignedLevelMVarsUsingErrorInfos levelMVars then
      throwAbortTerm
    throwMVarError <| m!"staged term contains unresolved metavariables\n\
      {MessageData.joinSep (mvars.toList.map MessageData.ofGoal) m!"\n\n"}"

/-- Elaborate `stx` under `hDen` and abstract it as a denotational component. -/
def elabDen (hDen : Expr) (stx : Syntax) (expectedType : Expr) : TermElabM Expr := do
  let body ← elabTermEnsuringType stx (some expectedType)
  mkLambdaFVars #[hDen] body

/-- Create a tactic metavariable whose finalizer runs once its target no longer
contains expression metavariables. -/
def mkPendingTacticMVar
    (type : Expr)
    (finalize : Expr → TermElabM Expr) : TermElabM Expr :=
  elabToSyntax
    (fun expectedType? => do
      let some expectedType := expectedType?
        | throwError "missing pending finalization target"
      finalize expectedType)
    (fun term => do
      let goal ← mkFreshExprMVar (some type) .syntheticOpaque
      let tacticCode ← `(by exact $term)
      registerSyntheticMVarWithCurrRef goal.mvarId! <|
        .tactic tacticCode (← saveContext) .term (delayOnMVars := true)
      return goal)

/-- `PendingCodeCheck.{u} stage index typeDen` -/
@[match_pattern]
def mkPendingCodeCheck (u : Level) (stage index typeDen : Expr) : Expr :=
  mkApp3 (.const ``PendingCodeCheck [u]) stage index typeDen

def finalizeCodeCheck (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingCodeCheck u stage index typeDen := target
    | throwError "malformed pending code check"
  let some stageValue := rawIntLit? stage | throwError "malformed pending code check"
  let codeType := mkCodeType u index typeDen
  ensureNoMVars codeType
  checkStages codeType (startStage := stageValue)
  return mkApp3 (.const ``PendingCodeCheck.done [u]) stage index typeDen

/-- `PendingQuoteAction.{u} stage index typeDen den` -/
@[match_pattern]
def mkPendingQuoteAction (u : Level) (stage index typeDen den : Expr) : Expr :=
  mkApp4 (.const ``PendingQuoteAction [u]) stage index typeDen den

/-- Finalize a pending quotation generator action. -/
def finalizeQuoteAction (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingQuoteAction u stage index typeDen den := target
    | throwError "malformed pending quotation action"
  let some stage := rawIntLit? stage | throwError "malformed pending quotation action"
  let gen := .app (mkConst ``Codegen.stub) index
  let quote := mkCode u index typeDen den gen
  ensureNoMVars quote
  Transform.compileQuote stage index quote

def evalSplice (stage : Int) (index splice : Expr) : TermElabM Expr := do
  let splice ← instantiateMVars splice
  ensureNoMVars splice
  Transform.evaluateSplice stage index splice

/--
For a context-owning quote that may be generative, create a pending generator
action. Otherwise, return a stub generator.
-/
def mkGen (u : Level) (stage : Int) (index typeDen den : Expr)
    (ownsContext : Bool) : TermElabM Expr := do
  if ownsContext then
    unless ← isDen index do
      let actionType := mkPendingQuoteAction u (mkRawIntLit stage) index typeDen den
      let action ← mkPendingTacticMVar actionType finalizeQuoteAction
      return mkApp2 (mkConst ``Codegen.mk) index action
  return .app (mkConst ``Codegen.stub) index

public section

syntax:lead (name := indexedCodeStx) "Code " term:arg : term
syntax:max (name := indexedQuoteStx) "`⟨" term "⟩" : term
syntax:max (name := indexedSpliceStx) "~" term:max : term

@[term_elab indexedCodeStx]
def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $typeStx) := stx | throwUnsupportedSyntax
  let u ← mkFreshLevelMVar
  if let some expectedType := expectedType? then
    discard <| isDefEq expectedType (.sort (.max .one u))
  let (ownsContext, index, stage, typeDen) ←
    enterDenContext (autoBind := true) fun _ hDen =>
      elabDen hDen typeStx (.sort u)
  if ownsContext then
    unless ← isDen index do
      let checkType := mkPendingCodeCheck u (mkRawIntLit stage) index typeDen
      discard <| mkPendingTacticMVar checkType finalizeCodeCheck
  let code := mkCodeType u index typeDen
  ensureHasType expectedType? code (errorMsgHeader? := "Code")

@[term_elab indexedQuoteStx]
def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$bodyStx⟩) := stx | throwUnsupportedSyntax
  let expectedType ← expectedType?.getDM mkFreshTypeMVar
  let u ← mkFreshLevelMVar
  let typeIndex ← mkFreshExprMVar (some (mkConst ``Interpretation))
  let typeDen ← mkFreshExprMVar (some (mkForallDen typeIndex (.sort u)))
  let codeType := mkCodeType u typeIndex typeDen
  discard <| isDefEq expectedType codeType
  let (ownsContext, index, stage, typeDen, den) ←
    enterDenContext fun contextIndex hDen => do
      discard <| isDefEq typeIndex contextIndex
      let typeDen ← whnf typeDen
      let den ← elabDen hDen bodyStx (← instantiateTypeDen typeDen hDen)
      return (typeDen, den)
  let gen ← mkGen u stage index typeDen den ownsContext
  let quote := mkCode u index typeDen den gen
  ensureHasType expectedType quote (errorMsgHeader? := "quotation")

@[term_elab indexedSpliceStx]
def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$codeStx) := stx | throwUnsupportedSyntax
  escapeDenContext fun isRoot stage index hDen => do
    let expectedType ← expectedType?.getDM mkFreshTypeMVar
    let u ← getLevel expectedType
    let typeDen ← mkLambdaFVars #[hDen] expectedType
    let codeType := mkCodeType u index typeDen
    if !isRoot then
      let code ← elabTermEnsuringType codeStx (some codeType)
      let splice := mkCodeDen u index typeDen code hDen
      return splice
    let code ← withoutErrToSorry <| withSynthesize do
      let code ← elabTerm codeStx (some codeType)
      if let some (mkApp2 _ codeIndex _) ← whnfUntil (← inferType code) ``«Code» then
        unless ← isDefEq codeIndex index do
          throwError "cannot splice code from a different staging context"
      ensureHasType (some codeType) code
    let code ← instantiateMVars code
    let typeDen ← instantiateMVars typeDen
    let splice := mkCodeDen u index typeDen code hDen
    let result ← evalSplice stage index splice
    let coeResult ← ensureHasType (some expectedType) result
    if ← checkCoherence.getM then
      let denotation ← splice.replaceFVarsM #[index, hDen]
        #[mkConst ``Interpretation.den, mkConst ``Den.intro]
      withNewMCtxDepth do
        unless ← isDefEq result denotation do
          let note ← mkUnfoldAxiomsNote result denotation
          throwError m!"generated code is not definitionally equal to its denotation\n\
            generated:{indentExpr result}\n\
            denotation:{indentExpr denotation}{note}"
    return coeResult

open PrettyPrinter Delaborator
open PrettyPrinter.Delaborator.SubExpr

@[app_delab «Code»]
def delabCode : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  let type ← withNaryArg 1 do
    let .lam name _ _ _ ← getExpr | failure
    withBindingBody name delab
  `(Code $type)

@[app_delab Code.mk]
def delabQuote : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
  let body ← withNaryArg 2 do
    let .lam name _ _ _ ← getExpr | failure
    withBindingBody name delab
  `(`⟨$body⟩)

@[app_delab Code.den]
def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
  let .fvar _ ← withNaryArg 3 getExpr | failure
  let body ← withNaryArg 2 delab
  `(~$body)

end

end

end TMeta.Elab
