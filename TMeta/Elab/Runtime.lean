module

public import TMeta.Codegen
public import Lean.EnvExtension
import Lean.Meta.Eval

open Lean Meta

namespace TMeta.Elab

public section

private unsafe def evalCodegenImpl (gen : Expr) : Codegen := do
  let result ← evalExpr Codegen (mkConst ``Codegen) gen
  result

@[implemented_by evalCodegenImpl]
opaque evalCodegen (gen : Expr) : Codegen

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

def withInstantiate (template : QuoteTemplate)
    (splices : Array β) (value : β → MetaM Expr)
    (k : MetaM α) : MetaM α := do
  unless template.spliceHoles.size = splices.size do
    throwError "staged quote expected {template.spliceHoles.size} splices, got {splices.size}"
  withMCtx template.mctx do
    for (hole, splice) in template.spliceHoles.zip splices do
      hole.assign (← value splice)
    k

end QuoteTemplate

def instantiateQuoteTemplate (declName : Name) (index : Nat)
    (spliceGens : Array (MetaM Expr)) : MetaM Expr := do
  let some quotes := quoteTemplatesExt.find? (← getEnv) declName
    | throwError "no staged quotes have been registered for declaration `{.ofConstName declName}`"
  let some quote := quotes[index]?
    | throwError "invalid staged quote index {index} for declaration `{.ofConstName declName}`"
  quote.withInstantiate spliceGens id <|
    instantiateMVars quote.body

end

end TMeta.Elab
