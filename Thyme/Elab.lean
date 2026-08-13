module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.PrettyPrinter.Delaborator.Builtins
public import Thyme.Syntax
public meta import Thyme.Elab.Context
public meta import Thyme.Elab.Common
public meta import Thyme.Elab.Check
public meta import Thyme.Elab.Runtime
public meta import Thyme.Elab.Transform
public import Thyme.Elab.Linter
public import Thyme.Code
public import Thyme.Elab.Check
public import Thyme.Elab.Transform
public import Thyme.Elab.Runtime
public import Thyme.Elab.Lemmas

open Lean Meta
open Thyme.Prelude

namespace Thyme.Elab

public inductive PendingCodeCheck
    (level : Int)
    (staged : Staged)
    (typeDen : staged.interp = .den → Sort u) : Prop where
  | done : PendingCodeCheck level staged typeDen

public abbrev PendingQuoteAction
    (_level : Int)
    (staged : Staged)
    (typeDen : staged.interp = .den → Sort u)
    (_den : (hDen : staged.interp = .den) → typeDen hDen)
    (_hGen : staged.interp = .gen) : Type :=
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

def isDen (staged : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq (mkStagedInterp staged) (mkConst ``Interp.den)

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

/-- `PendingCodeCheck.{u} level staged typeDen` -/
@[match_pattern]
def mkPendingCodeCheck (u : Level) (level staged typeDen : Expr) : Expr :=
  mkApp3 (.const ``PendingCodeCheck [u]) level staged typeDen

def finalizeCodeCheck (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingCodeCheck u level staged typeDen := target
    | throwError "malformed pending code check"
  let some levelValue := rawIntLit? level | throwError "malformed pending code check"
  let codeType := mkCodeType u staged typeDen
  ensureNoMVars codeType
  checkStages codeType (startLevel := levelValue)
  return mkApp3 (.const ``PendingCodeCheck.done [u]) level staged typeDen

/-- `PendingQuoteAction.{u} level staged typeDen den hGen` -/
@[match_pattern]
def mkPendingQuoteAction (u : Level) (level staged typeDen den hGen : Expr) : Expr :=
  mkApp5 (.const ``PendingQuoteAction [u]) level staged typeDen den hGen

/-- Finalize a pending quotation generator action. -/
def finalizeQuoteAction (target : Expr) : TermElabM Expr := do
  let target ← instantiateMVars target
  let mkPendingQuoteAction u level staged typeDen den hGen := target
    | throwError "malformed pending quotation action"
  let some level := rawIntLit? level | throwError "malformed pending quotation action"
  let gen := .app (mkConst ``Codegen.stub) (mkStagedInterp staged)
  let quote := mkCode u staged typeDen den gen
  ensureNoMVars quote
  compileQuote level staged hGen quote

def evalSplice (level : Int) (staged splice : Expr) : TermElabM Expr := do
  let splice ← instantiateMVars splice
  ensureNoMVars splice
  evaluateSplice level staged splice

/--
For a context-owning quote that may be generative, create a pending generator
action. Otherwise, return a stub generator.
-/
def mkGen (u : Level) (level : Int) (staged typeDen den : Expr)
    (ownsContext : Bool) : TermElabM Expr := do
  if ownsContext then
    unless ← isDen staged do
      let hGenName ← mkFreshUserName hGenName
      let action ← withLocalDeclD hGenName (mkEqGen staged) fun hGen => do
        let actionType :=
          mkPendingQuoteAction u (mkRawIntLit level) staged typeDen den hGen
        let actionBody ← mkPendingTacticMVar actionType finalizeQuoteAction
        mkLambdaFVars #[hGen] actionBody
      return mkApp2 (mkConst ``Codegen.mk) (mkStagedInterp staged) action
  return .app (mkConst ``Codegen.stub) (mkStagedInterp staged)

public section

@[term_elab Thyme.Prelude.codeStx]
def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $typeStx) := stx | throwUnsupportedSyntax
  let u ← mkFreshLevelMVar
  if let some expectedType := expectedType? then
    discard <| isDefEq expectedType (.sort (.max .one u))
  let (ownsContext, staged, level, typeDen) ←
    enterDenContext fun _ hDen =>
      elabDen hDen typeStx (.sort u)
  if ownsContext then
    unless ← isDen staged do
      let checkType := mkPendingCodeCheck u (mkRawIntLit level) staged typeDen
      discard <| mkPendingTacticMVar checkType finalizeCodeCheck
  let code := mkCodeType u staged typeDen
  ensureHasType expectedType? code (errorMsgHeader? := "Code")

@[term_elab Thyme.Prelude.quoteStx]
def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$bodyStx⟩) := stx | throwUnsupportedSyntax
  let expectedType ← expectedType?.getDM mkFreshTypeMVar
  let u ← mkFreshLevelMVar
  let codeStaged ← mkFreshExprMVar (some (mkConst ``Staged))
  let (ownsContext, staged, level, typeDen, den) ←
    enterDenContext fun contextStaged hDen => do
      discard <| isDefEq codeStaged contextStaged
      let typeDenBody ← mkFreshExprMVar (some (.sort u))
      let typeDen ← mkLambdaFVars #[hDen] typeDenBody
      let codeType := mkCodeType u codeStaged typeDen
      discard <| isDefEq expectedType codeType
      let den ← elabDen hDen bodyStx typeDenBody
      return (typeDen, den)
  let gen ← mkGen u level staged typeDen den ownsContext
  let quote := mkCode u staged typeDen den gen
  ensureHasType expectedType quote (errorMsgHeader? := "quotation")

@[term_elab Thyme.Prelude.spliceStx]
def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$codeStx) := stx | throwUnsupportedSyntax
  escapeDenContext fun isRoot level staged hDen => do
    let expectedType ← expectedType?.getDM mkFreshTypeMVar
    let u ← getLevel expectedType
    let typeDen ← mkLambdaFVars #[hDen] expectedType
    let codeType := mkCodeType u staged typeDen
    if !isRoot then
      let code ← elabTermEnsuringType codeStx (some codeType)
      let splice := mkCodeDen u staged typeDen code hDen
      return splice
    let code ← withoutErrToSorry <| withSynthesize do
      let code ← elabTerm codeStx (some codeType)
      if let some (mkApp2 _ codeStaged _) ← whnfUntil (← inferType code) ``«Code» then
        unless ← isDefEq codeStaged staged do
          throwError "cannot splice code from a different staging context"
      ensureHasType (some codeType) code
    let code ← instantiateMVars code
    let typeDen ← instantiateMVars typeDen
    let splice := mkCodeDen u staged typeDen code hDen
    let result ← evalSplice level staged splice
    let coeResult ← ensureHasType (some expectedType) result
    if ← checkCoherence.getM then
      let code ← code.replaceFVarsM #[staged, hDen]
        #[mkStaged (mkConst ``Interp.den), ← mkEqRefl (mkConst ``Interp.den)]
      let denotation ← mkAppM ``Code.den #[code]
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

@[app_delab Code.den']
def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 4 do
  let .fvar _ ← withNaryArg 3 getExpr | failure
  let body ← withNaryArg 2 delab
  `(~$body)

end

end

end Thyme.Elab
