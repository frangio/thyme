module

public import TMeta.Elab.Runtime
public meta import TMeta.Code
public meta import TMeta.Elab.Check
public meta import TMeta.Elab.Transform
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term.TermElabM

namespace TMeta

meta section

open Lean Elab Term Meta

public meta register_option tmeta.raw : Bool := {
  defValue := false
  descr := "elaborate TMeta syntax without compiling it"
}

def withCodeReducible (k : TermElabM α) : TermElabM α := do
  let quoteStatus ← getReducibilityStatus ``Code.quote
  let valueStatus ← getReducibilityStatus ``Code.value
  try
    setReducibilityStatus ``Code.quote .reducible
    setReducibilityStatus ``Code.value .reducible
    k
  finally
    setReducibilityStatus ``Code.quote quoteStatus
    setReducibilityStatus ``Code.value valueStatus

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

def elabStagedTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  if ← tmeta.raw.getM then
    elabTermEnsuringType stx expectedType?
  else
    let expectedType ← expectedType?.getDM mkFreshTypeMVar
    let raw ← withCodeReducible <|
      withOptions (tmeta.raw.set · true) <|
        instantiateMVars <=< withSynthesize <|
          elabTermEnsuringType stx (some expectedType)
    let expectedType ← instantiateMVars expectedType
    ensureNoMVars raw
    ensureNoMVars expectedType
    checkStages raw
    let lctx ← instantiateLCtxMVars (← getLCtx)
    let localInstances ← getLocalInstances
    let ctx : TransformContext := {
      hFalse? := none
    }
    let state := TransformState.initial
    let (result, _) ← withLCtx lctx localInstances <| withMCtx {} <| StateT.run
      ((transform (.expect expectedType #[]) raw) ctx) state
    ensureHasType expectedType? result

public section

syntax:max (name := codeStx) "Code " term:arg : term
syntax:max (name := bareCodeStx) "Code" : term
syntax:max (name := quoteStx) "`⟨" term "⟩" : term
syntax:max (name := spliceStx) "~" term:max : term

@[term_elab codeStx]
meta def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $type) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code $type)) expectedType?

@[term_elab bareCodeStx]
meta def elabBareCode : TermElab := fun stx expectedType? => do
  elabTerm (mkIdentFrom stx ``TMeta.Code) expectedType?

@[term_elab quoteStx]
meta def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$value⟩) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code.quote $value)) expectedType?

@[term_elab spliceStx]
meta def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$body) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code.value $body)) expectedType?

end

end

end TMeta
