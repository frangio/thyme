module

public import Lean.Elab.Term.TermElabM

open Lean Meta Elab Term

namespace Thyme.Elab

/--
Invokes the continuation with fresh free variables with the given names, then
abstracts the result into a lambda. The variables carry dummy types in the
local context and in the resulting lambda binders, so the term will be
ill-typed until the binders are beta-instantiated away with appropriately typed
values.
-/
public def mkLambdaFreshFVars (names : Array Name)
    (k : Array Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclsDND (names.map (·, .sort .zero)) fun fresh => do
    mkLambdaFVars fresh (← k fresh)

structure QuoteTemplate where
  levelParams : Array Name
  body : Expr

initialize quoteTemplatesExt : MapDeclarationExtension (Array QuoteTemplate) ←
  mkMapDeclarationExtension (asyncMode := .local)

public def instantiateQuoteTemplate (declName : Name) (templateIndex : Nat)
    (captures : Array Expr) (splices : Array (MetaM Expr)) : MetaM Expr := do
  let env ← getEnv
  let some template := quoteTemplatesExt.find? env declName |>.bind (·[templateIndex]?)
    | throwError "quote #{templateIndex} for `{.ofConstName declName}` not found"
  let levels ← template.levelParams.mapM fun _ => mkFreshLevelMVar
  let body := template.body.instantiateLevelParamsArray template.levelParams levels
  let splices ← splices.mapM id
  let args := captures ++ splices
  return body.instantiateBetaRevRange 0 args.size args

/--
Registers a quote template under the declaration being elaborated, and returns
`instantiateQuoteTemplate` partially applied to the lookup parameters, with
type `Array Expr → Array (MetaM Expr) → MetaM Expr`.
-/
public def registerQuoteTemplate (template : Expr) : TermElabM Expr := do
  if template.hasMVar then
    throwError "internal staging error: quote template contains metavariables"
  let levelParams := (collectLevelParams {} template).params
  let declName := (← getDeclName?).getD .anonymous
  let templates := quoteTemplatesExt.find? (← getEnv) declName |>.getD #[]
  let index := templates.size
  modifyEnv fun env => quoteTemplatesExt.insert env declName
    (templates.push { levelParams, body := template })
  return mkApp2 (mkConst ``instantiateQuoteTemplate) (toExpr declName) (toExpr index)

end Thyme.Elab
