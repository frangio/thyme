module

public import Lean.EnvExtension
public import Lean.Meta.Basic

open Lean Meta

namespace Staging

public section

structure QuoteTemplate where
  mctx : MetavarContext
  body : Expr
  spliceHoles : Array MVarId

initialize quoteTemplatesExt : MapDeclarationExtension (Array QuoteTemplate) ←
  mkMapDeclarationExtension (asyncMode := .local)

def registerQuoteTemplate [Monad m] [MonadEnv m]
    (declName : Name) (quote : QuoteTemplate) : m Nat := do
  let quotes := quoteTemplatesExt.find? (← getEnv) declName |>.getD #[]
  let index := quotes.size
  modifyEnv fun env => quoteTemplatesExt.insert env declName (quotes.push quote)
  return index

def instantiateQuoteTemplate (declName : Name) (index : Nat)
    (spliceGens : Array (MetaM Expr)) : MetaM Expr := do
  let some quotes := quoteTemplatesExt.find? (← getEnv) declName
    | throwError "no staged quotes have been registered for declaration `{.ofConstName declName}`"
  let some quote := quotes[index]?
    | throwError "invalid staged quote index {index} for declaration `{.ofConstName declName}`"
  unless quote.spliceHoles.size = spliceGens.size do
    throwError "staged quote expected {quote.spliceHoles.size} generators, got {spliceGens.size}"
  withMCtx quote.mctx do
    for (hole, spliceGen) in quote.spliceHoles.zip spliceGens do
      hole.assign (← spliceGen)
    instantiateMVars quote.body

end

end Staging
