module

public meta import Lean.Elab.Tactic.Guard

open Lean Elab Command Term Meta
open Lean.Parser Lean.Parser.Tactic Lean.Parser.Command
open Lean.Elab.Tactic.GuardExpr

/-- Variant of `#guard_expr` that prints elaborated terms on error. -/
elab "#guard_staged " r:term:51 eq:equal p:term : command =>
  runTermElabM fun _ => Term.withoutErrToSorry do
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    let r ← elabTerm r none
    let p ← elabTerm p none
    _ ← isDefEqGuarded (← inferType r) (← inferType p)
    synthesizeSyntheticMVarsNoPostponing
    let r ← instantiateMVars r
    let p ← instantiateMVars p
    let res ← mk.isEq r p
    unless res do throwError m!"Elaborated term:{indentExpr r}\n\
      is not {mk.toStringDescr} expected term:{indentExpr p}"
