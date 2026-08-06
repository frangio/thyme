module

public import TMeta.Code
public import Lean.Elab.Term.TermElabM
import Lean.Meta.InferType

open Lean Meta

namespace TMeta.Elab

structure QuoteTemplate where
  body : Expr
  spliceFVars : Array (Array Expr)

initialize quoteTemplatesExt : MapDeclarationExtension (Array QuoteTemplate) ←
  mkMapDeclarationExtension (asyncMode := .local)

def QuoteTemplate.instantiate {i : Interpretation} (template : QuoteTemplate)
    (hGen : i = .gen) (splices : Array (Codegen i)) : MetaM Expr := do
  if h : template.spliceFVars.size = splices.size then
    let splices ← template.spliceFVars.mapFinIdxM fun i fvars hi => do
      let value ← splices[i].run hGen
      return fvars.size.repeat
        (.lam .anonymous (.sort .zero) · .default)
        (value.abstract fvars)
    return template.body.instantiateBetaRevRange 0 splices.size splices
  else
    throwError "staged quote expected {template.spliceFVars.size} splices, got {splices.size}"

public def instantiateQuoteTemplate (declName : Name) (templateIndex : Nat)
    (i : Interpretation) (hGen : i = .gen)
    (splices : Array (Codegen i)) : MetaM Expr := do
  let env ← getEnv
  let some template := quoteTemplatesExt.find? env declName |>.bind (·[templateIndex]?)
    | throwError "quote #{templateIndex} for `{.ofConstName declName}` not found"
  template.instantiate hGen splices

/-- Registers a quote template and returns an expression of type
`(i : Interpretation) → i = .gen → Array (Codegen i) → MetaM Expr`. -/
public def registerQuoteTemplate (template : Expr)
    (spliceFVars : Array (Array Expr)) : Lean.Elab.Term.TermElabM Expr := do
  let declName := (← Lean.Elab.Term.getDeclName?).getD .anonymous
  let templates := quoteTemplatesExt.find? (← getEnv) declName |>.getD #[]
  let index := templates.size
  modifyEnv fun env =>
    quoteTemplatesExt.insert env declName (templates.push ⟨template, spliceFVars⟩)
  return mkApp2 (mkConst ``instantiateQuoteTemplate)
    (toExpr declName) (toExpr index)

end TMeta.Elab
