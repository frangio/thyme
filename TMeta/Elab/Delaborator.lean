module

public import TMeta.Elab.Term
public meta import TMeta.Code
public meta import Lean.PrettyPrinter.Delaborator

namespace TMeta

public meta section

open Lean PrettyPrinter Delaborator
open PrettyPrinter.Delaborator.SubExpr

register_option pp.spliceNotation : Bool := {
  defValue := false
  descr := "delaborate Code.val applications using splice notation"
}

private def withSpliceNotation (x : DelabM α) : DelabM α :=
  withOptions (pp.spliceNotation.set · true) x

@[app_delab TMeta.Code]
meta def delabCode : Delab := do
  match (← getExpr).getAppNumArgs with
  | 0 =>
    `(Code)
  | 1 =>
    let type ← withNaryArg 0 <| withSpliceNotation delab
    `(Code $type)
  | _ =>
    failure

@[app_delab Code.quote]
meta def delabQuote : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
  let value ← withNaryArg 1 <| withSpliceNotation delab
  `(`⟨$value⟩)

@[app_delab Code.val]
meta def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  guard (← pp.spliceNotation.getM)
  let body ← withNaryArg 1 delab
  `(~$body)

@[app_delab ExfCodegen.squash]
meta def delabExfCodegenSquash : Delab := withOverApp 1 do
  `(⋯)

@[app_delab ExfCodegen.default]
meta def delabExfCodegenDefault : Delab := `(⋯)

end

end TMeta
