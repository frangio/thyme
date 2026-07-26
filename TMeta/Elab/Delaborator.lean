module

public import TMeta.Elab.Term
public meta import TMeta.Code
public meta import Lean.PrettyPrinter.Delaborator

namespace TMeta.Elab

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

@[app_delab Code.mk!]
meta def delabQuote : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
  let value ← withNaryArg 1 do
    let .lam _ type body _ ← getExpr | failure
    guard (type.isConstOf ``Unit)
    guard (!body.hasLooseBVars)
    descend body 1 <| withSpliceNotation delab
  `(`⟨$value⟩)

@[app_delab Code.val]
meta def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  guard (← pp.spliceNotation.getM)
  let body ← withNaryArg 1 delab
  `(~$body)

private def delabCodegen (arity : Nat) : Delab := withOverApp arity do
  `(⋯)

@[app_delab Codegen.abs]
meta def delabCodegenAbs : Delab := delabCodegen 2

@[app_delab Codegen.mk]
meta def delabCodegenMk : Delab := delabCodegen 1

@[app_delab Codegen.stub]
meta def delabCodegenStub : Delab := delabCodegen 0

end

end TMeta.Elab
