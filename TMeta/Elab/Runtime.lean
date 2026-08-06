module

public import TMeta.Codegen
import Lean.Util.CollectMVars
import Lean.Meta.InferType

open Lean Meta

namespace TMeta.Elab

structure QuoteTemplate where
  body : Expr
  spliceFVars : Array (Array Expr)

initialize quoteTemplatesExt : MapDeclarationExtension (Array QuoteTemplate) ←
  mkMapDeclarationExtension (asyncMode := .local)

structure PendingSplice where
  index : Nat
  mvarId : MVarId
  fvars : Array Expr

def mkQuoteTemplate (body : Expr) : MetaM QuoteTemplate := do
  let mvarIds := body.collectMVars {} |>.result
  let splices ← mvarIds.mapM fun mvarId => do
    let (root, fvars) ← match ← getDelayedMVarAssignment? mvarId with
      | some { mvarIdPending, fvars } => pure (mvarIdPending, fvars)
      | none => pure (mvarId, #[])
    if ← root.isDelayedAssigned then
      throwError "unexpected delayed metavariable chain in quote template"
    let decl ← root.getDecl
    return { index := decl.index, mvarId, fvars : PendingSplice }
  let splices := splices.qsort fun a b => a.index < b.index
  return {
    body := body.abstract (splices.map (.mvar ·.mvarId))
    spliceFVars := splices.map (·.fvars)
  }

def QuoteTemplate.instantiate (template : QuoteTemplate) (splices : Array Codegen) :
    MetaM Expr := do
  unless template.spliceFVars.size = splices.size do
    throwError "staged quote expected {template.spliceFVars.size} splices, got {splices.size}"
  let splices ← template.spliceFVars.zipWithM splices (f := fun fvars splice => do
    let value ← splice.run
    return fvars.size.repeat
      (.lam .anonymous (.sort .zero) · .default)
      (value.abstract fvars))
  return template.body.instantiateBetaRevRange 0 splices.size splices

public def registerQuoteTemplate (declName : Name) (body : Expr) : MetaM Nat := do
  let template ← mkQuoteTemplate body
  let templates := quoteTemplatesExt.find? (← getEnv) declName |>.getD #[]
  let index := templates.size
  modifyEnv fun env => quoteTemplatesExt.insert env declName (templates.push template)
  return index

public def instantiateQuoteTemplate (declName : Name) (index : Nat)
    (splices : Array Codegen) : MetaM Expr := do
  let env ← getEnv
  let some quote := quoteTemplatesExt.find? env declName |>.bind (·[index]?)
    | throwError "quote #{index} for `{.ofConstName declName}` not found"
  quote.instantiate splices

end TMeta.Elab
