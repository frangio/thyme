module

public import Lean.Meta.Basic
import Thyme.Code

open Lean Meta

namespace Thyme.Elab

public section

def hDenName : Name := `hDen
def hGenName : Name := `hGen
def instStagedName : Name := `s

def throwMultiLevelStagingError [Monad m] [MonadError m] : m α :=
  throwError "staging error: multi-level staging is not supported"

/-- `instStaged.interp` -/
def mkStagedInterp (instStaged : Expr) : Expr :=
  .app (mkConst ``Staged.interp) instStaged

/-- `Staged.mk interp` -/
def mkStaged (interp : Expr) : Expr :=
  .app (mkConst ``Staged.mk) interp

/-- `instStaged.interp = Interp.den` -/
def mkEqDen (instStaged : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) (mkStagedInterp instStaged)
    (mkConst ``Interp.den)

/-- `fun _ : instStaged.interp = Interp.den => PUnit.{u}` -/
def mkErasedTypeDen (u : Level) (instStaged : Expr) : Expr :=
  .lam hDenName (mkEqDen instStaged) (.const ``PUnit [u]) .default

/-- `typeDen hDen`, exposing a reducible family and its head beta redex. -/
def instantiateTypeDen (typeDen hDen : Expr) : MetaM Expr := do
  match ← whnf typeDen with
  | .lam _ _ body _ =>
    return body.instantiate1 hDen
  | typeDen =>
    return .app typeDen hDen

/-- `Code.{u} instStaged typeDen` -/
def mkCodeType (u : Level) (instStaged typeDen : Expr) : Expr :=
  mkApp2 (.const ``Code [u]) instStaged typeDen

/-- `Code.mk instStaged typeDen den gen` -/
def mkCode (u : Level) (instStaged typeDen den gen : Expr) : Expr :=
  mkApp4 (.const ``Code.mk [u]) instStaged typeDen den gen

/-- `Code.den' instStaged typeDen code hDen` -/
def mkCodeDen (u : Level) (instStaged typeDen code hDen : Expr) : Expr :=
  mkApp4 (.const ``Code.den' [u]) instStaged typeDen code hDen

/-- `instStaged.interp = Interp.gen` -/
def mkEqGen (instStaged : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) (mkStagedInterp instStaged)
    (mkConst ``Interp.gen)

end

end Thyme.Elab
