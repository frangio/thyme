module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public meta import Thyme.Elab.Context
public meta import Thyme.Elab.Common
public meta import Thyme.Elab.Transform -- shake: keep
public meta import Thyme.Elab.Check -- shake: keep
public import Thyme.Code
public import Thyme.Syntax
public import Thyme.Elab.Lemmas
public import Thyme.Elab.QuoteTemplate

open Lean Meta
open PrettyPrinter Delaborator
open PrettyPrinter.Delaborator.SubExpr

open Thyme.Prelude

namespace Thyme.Elab

public inductive PendingCodeCheck
    (stage : Int)
    (interp : Interp)
    (typeDen : interp = .den → Sort u) : Prop where
  | done : PendingCodeCheck stage interp typeDen

public abbrev PendingQuoteAction
    (_stage : Int)
    (interp : Interp)
    (typeDen : interp = .den → Sort u)
    (_den : (hDen : interp = .den) → typeDen hDen)
    (_hGen : interp = .gen) : Type :=
  MetaM Expr

meta section

open Lean Elab Meta
open Lean.Elab.Term hiding mkConst

public register_option thyme.checkCoherence : Bool := {
  defValue := false
  descr := "check that generated code is definitionally equal to its denotation"
}

def checkCoherence : Lean.Option Bool where
  name := `thyme.checkCoherence
  defValue := false

def isDen (interp : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq interp (mkConst ``Interp.den)

def ensureSpliceInterp (code expectedInterp : Expr) : TermElabM Unit := do
  let some (mkApp2 _ actualInterp _) ← whnfUntil (← inferType code) ``«Code»
    | throwError "code expected"
  unless ← isDefEq actualInterp expectedInterp do
    if ← isDen actualInterp then
      throwError "cannot splice denotational code; the declaration that produced it may be \
        missing a `[Staged]` parameter"
    else
      throwError "cannot splice code from a different staging context"

def ensureNoMVars (e : Expr) : TermElabM Unit := do
  if e.hasMVar then
    tryPostpone
    let mvars ← getMVars e
    if ← logUnassignedUsingErrorInfos mvars then
      throwAbortTerm
    let levelMVars := (collectLevelMVars {} e).result
    if ← logUnassignedLevelMVarsUsingErrorInfos levelMVars then
      throwAbortTerm
    let e ← exposeLevelMVars (← instantiateMVars e)
    let msg := if mvars.isEmpty then
      m!"staged term contains unresolved universe levels{indentExpr e}"
    else
      m!"staged term contains unresolved metavariables{indentExpr e}\n\
        {MessageData.joinSep (mvars.toList.map MessageData.ofGoal) m!"\n\n"}"
    throwMVarError msg

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

/-- `PendingCodeCheck.{u} stage interp typeDen` -/
@[match_pattern]
def mkPendingCodeCheck (u : Level) (stage interp typeDen : Expr) : Expr :=
  mkApp3 (.const ``PendingCodeCheck [u]) stage interp typeDen

def finalizeCodeCheck (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingCodeCheck u stage interp typeDen := target
    | throwError "malformed pending code check"
  let some stageValue := rawIntLit? stage | throwError "malformed pending code check"
  let codeType := mkCodeType u interp typeDen
  ensureNoMVars codeType
  checkStages codeType (startStage := stageValue)
  return mkApp3 (.const ``PendingCodeCheck.done [u]) stage interp typeDen

/-- `PendingQuoteAction.{u} stage interp typeDen den hGen` -/
@[match_pattern]
def mkPendingQuoteAction (u : Level) (stage interp typeDen den hGen : Expr) : Expr :=
  mkApp5 (.const ``PendingQuoteAction [u]) stage interp typeDen den hGen

/-- Finalize a pending quotation generator action. -/
def finalizeQuoteAction (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingQuoteAction u stage interp typeDen den hGen := target
    | throwError "malformed pending quotation action"
  let some stage := rawIntLit? stage | throwError "malformed pending quotation action"
  let gen := .app (mkConst ``Codegen.stub) interp
  let quote := mkCode u interp typeDen den gen
  ensureNoMVars quote
  compileQuote stage interp hGen quote

def evalSplice (stage : Int) (instStaged splice : Expr) : TermElabM Expr := do
  let splice ← instantiateMVars splice
  ensureNoMVars splice
  evaluateSplice stage instStaged splice

/--
For a context-owning quote that may be generative, create a pending generator
action. Otherwise, return a stub generator.
-/
def mkGen (u : Level) (stage : Int) (interp typeDen den : Expr)
    (ownsContext : Bool) : TermElabM Expr := do
  if ownsContext then
    unless ← isDen interp do
      let hGenName ← mkFreshUserName hGenName
      let action ← withLocalDeclD hGenName (mkEqGen interp) fun hGen => do
        let actionType :=
          mkPendingQuoteAction u (mkRawIntLit stage) interp typeDen den hGen
        let actionBody ← mkPendingTacticMVar actionType finalizeQuoteAction
        mkLambdaFVars #[hGen] actionBody
      return mkApp2 (mkConst ``Codegen.mk) interp action
  return .app (mkConst ``Codegen.stub) interp

def freshenExprMVars (e : Expr) : MetaM Expr := do
  let e ← abstractMVars e (levels := false)
  let (_, _, e) ← openAbstractMVarsResult e
  pure e

public section

@[term_elab Thyme.Prelude.codeStx]
def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $typeStx) := stx | throwUnsupportedSyntax
  let u ← mkFreshLevelMVar
  if let some expectedType := expectedType? then
    discard <| isDefEq expectedType (.sort (.max .one u))
  let (ownsContext, instStaged, stage, typeDen) ←
    enterDenContext fun _ hDen =>
      elabDen hDen typeStx (.sort u)
  let interp := mkStagedInterp instStaged
  if ownsContext then
    unless ← isDen interp do
      let checkType := mkPendingCodeCheck u (mkRawIntLit stage) interp typeDen
      discard <| mkPendingTacticMVar checkType finalizeCodeCheck
  let code := mkCodeType u interp typeDen
  ensureHasType expectedType? code (errorMsgHeader? := "Code")

@[term_elab Thyme.Prelude.quoteStx]
def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$bodyStx⟩) := stx | throwUnsupportedSyntax
  let expectedType ← expectedType?.getDM mkFreshTypeMVar
  let u ← mkFreshLevelMVar
  let codeInterp ← mkFreshExprMVar (some (mkConst ``Interp))
  let (ownsContext, instStaged, stage, typeDen, den) ←
    enterDenContext fun contextInstStaged hDen => do
      discard <| isDefEq codeInterp (mkStagedInterp contextInstStaged)
      let typeDenBody ← mkFreshExprMVar (some (.sort u))
      let typeDen ← mkLambdaFVars #[hDen] typeDenBody
      let codeType := mkCodeType u codeInterp typeDen
      discard <| isDefEq expectedType codeType
      let den ← elabDen hDen bodyStx typeDenBody
      return (typeDen, den)
  let interp := mkStagedInterp instStaged
  let gen ← mkGen u stage interp typeDen den ownsContext
  let quote := mkCode u interp typeDen den gen
  ensureHasType expectedType quote (errorMsgHeader? := "quotation")

@[term_elab Thyme.Prelude.spliceStx]
def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$codeStx) := stx | throwUnsupportedSyntax
  escapeDenContext fun isRoot stage instStaged hDen => do
    if !isRoot then
      let typeDenBody ← expectedType?.getDM mkFreshTypeMVar
      let u ← getLevel typeDenBody
      let typeDen ← mkLambdaFVars #[hDen] typeDenBody
      let interp := mkStagedInterp instStaged
      let codeType := mkCodeType u interp typeDen
      let code ← elabTermEnsuringType codeStx (some codeType)
      let splice := mkCodeDen u interp typeDen code hDen
      return splice
    else
      let typeDenBody ← if let some expectedType := expectedType? then
        freshenExprMVars expectedType
      else
        mkFreshTypeMVar
      let u ← getLevel typeDenBody
      let typeDen ← mkLambdaFVars #[hDen] typeDenBody
      let interp := mkStagedInterp instStaged
      let codeType := mkCodeType u interp typeDen
      let code ← withoutErrToSorry <| withSynthesize do
        let code ← elabTerm codeStx (some codeType)
        ensureSpliceInterp code interp
        ensureHasType (some codeType) code
      let code ← instantiateMVars code
      let typeDenBody ← instantiateMVars typeDenBody
      let typeDen ← mkLambdaFVars #[hDen] typeDenBody
      let splice := mkCodeDen u interp typeDen code hDen
      let result ← evalSplice stage instStaged splice
      let coeResult ← ensureHasType expectedType? result
      if ← checkCoherence.getM then
        let code ← code.replaceFVarsM #[instStaged, hDen]
          #[mkStaged (mkConst ``Interp.den), ← mkEqRefl (mkConst ``Interp.den)]
        let denotation ← mkAppM ``Code.den #[code]
        withNewMCtxDepth do
          unless ← isDefEq result denotation do
            let note ← mkUnfoldAxiomsNote result denotation
            throwError m!"generated code is not definitionally equal to its denotation\n\
              generated:{indentExpr result}\n\
              denotation:{indentExpr denotation}{note}"
      return coeResult

@[app_delab «Code»]
def delabCode : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  let interp ← withNaryArg 0 getExpr
  withNewMCtxDepth do
    let .some instStaged ← trySynthInstance (mkConst ``Staged) | failure
    unless ← isDefEq interp (mkStagedInterp instStaged) do failure
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

@[app_delab Code.den']
def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
  let .fvar _ ← withNaryArg 3 getExpr | failure
  let body ← withNaryArg 2 delab
  `(~$body)

end

end

end Thyme.Elab
