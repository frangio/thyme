module

public import TMeta.Codegen

open Lean Meta

namespace TMeta.Elab

public section

structure QuoteTemplate where
  mctx : MetavarContext
  body : Expr
  spliceHoles : Array MVarId

initialize quoteTemplatesExt : MapDeclarationExtension (Array QuoteTemplate) ←
  mkMapDeclarationExtension (asyncMode := .local)

namespace QuoteTemplate

def register [Monad m] [MonadEnv m]
    (quote : QuoteTemplate) (declName : Name) : m Nat := do
  let quotes := quoteTemplatesExt.find? (← getEnv) declName |>.getD #[]
  let index := quotes.size
  modifyEnv fun env => quoteTemplatesExt.insert env declName (quotes.push quote)
  return index

def instantiate (template : QuoteTemplate)
    (splices : Array β) (value : β → MetaM Expr) : MetaM Expr := do
  unless template.spliceHoles.size = splices.size do
    throwError "staged quote expected {template.spliceHoles.size} splices, got {splices.size}"
  withMCtx template.mctx do
    for (hole, splice) in template.spliceHoles.zip splices do
      hole.assign (← value splice)
    instantiateMVars template.body

end QuoteTemplate

def instantiateQuoteTemplate (declName : Name) (index : Nat)
    (spliceGens : Array Codegen) : MetaM Expr := do
  let some quotes := quoteTemplatesExt.find? (← getEnv) declName
    | throwError "no staged quotes have been registered for declaration `{.ofConstName declName}`"
  let some quote := quotes[index]?
    | throwError "invalid staged quote index {index} for declaration `{.ofConstName declName}`"
  quote.instantiate spliceGens Codegen.run

end

end TMeta.Elab
