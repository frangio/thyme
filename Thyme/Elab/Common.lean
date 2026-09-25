module

public import Lean.Meta.Basic
import Lean.Meta.WHNF
import Thyme.Code

open Lean Meta

namespace Thyme.Elab

public section

def hDenName : Name := `hDen
def hGenName : Name := `hGen
def instStagedName : Name := `s

def throwMultiLevelStagingError [Monad m] [MonadError m] : m α :=
  throwError "staging error: multi-level staging is not supported"

/-- `instStaged.Den` -/
def mkStagedDen (instStaged : Expr) : Expr :=
  .app (mkConst ``Staged.Den) instStaged

def mkStagedGen (instStaged : Expr) : Expr :=
  .app (mkConst ``Staged.Gen) instStaged

/-- `fun _ : instStaged.Den => PUnit.{u}` -/
def mkErasedTypeDen (u : Level) (instStaged : Expr) : Expr :=
  .lam hDenName (mkStagedDen instStaged) (.const ``PUnit [u]) .default

/-- `typeDen hDen`, exposing a reducible family and its head beta redex. -/
def instantiateTypeDen (typeDen hDen : Expr) : MetaM Expr := do
  match ← whnf typeDen with
  | .lam _ _ body _ =>
    return body.instantiate1 hDen
  | typeDen =>
    return .app typeDen hDen

/-- `@Code.{u} instStaged typeDen` -/
def mkCodeType (u : Level) (instStaged typeDen : Expr) : Expr :=
  mkApp2 (.const ``Code [u]) instStaged typeDen

def whnfCodeType? (type : Expr) : MetaM (Option (Level × Expr × Expr)) := do
  let some type ← whnfUntil type ``«Code» | return none
  let mkApp2 (.const _ [u]) instStaged typeDen := type
    | throwError "malformed Code type"
  return some (u, instStaged, typeDen)

/-- `@Code.mk.{u} instStaged typeDen den gen` -/
def mkCode (u : Level) (instStaged typeDen den gen : Expr) : Expr :=
  mkApp4 (.const ``Code.mk [u]) instStaged typeDen den gen

/-- `@Code.den'.{u} instStaged typeDen code hDen` -/
def mkCodeDen (u : Level) (instStaged typeDen code hDen : Expr) : Expr :=
  mkApp4 (.const ``Code.den' [u]) instStaged typeDen code hDen

end

end Thyme.Elab
