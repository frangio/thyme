module

public import Lean.Meta.Basic
import Thyme.Code

open Lean Meta

namespace Thyme.Elab

public section

def hDenName : Name := `hDen
def hGenName : Name := `hGen
def stagedName : Name := `s

def throwMultiLevelStagingError [Monad m] [MonadError m] : m α :=
  throwError "staging error: multi-level staging is not supported"

/-- `staged.interp` -/
def mkStagedInterp (staged : Expr) : Expr :=
  .app (mkConst ``Staged.interp) staged

/-- `Staged.mk interp` -/
def mkStaged (interp : Expr) : Expr :=
  .app (mkConst ``Staged.mk) interp

/-- `staged.interp = Interp.den` -/
def mkEqDen (staged : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) (mkStagedInterp staged)
    (mkConst ``Interp.den)

/-- `fun _ : staged.interp = Interp.den => PUnit.{u}` -/
def mkErasedTypeDen (u : Level) (staged : Expr) : Expr :=
  .lam hDenName (mkEqDen staged) (.const ``PUnit [u]) .default

/-- `typeDen hDen`, exposing a reducible family and its head beta redex. -/
def instantiateTypeDen (typeDen hDen : Expr) : MetaM Expr := do
  match ← whnf typeDen with
  | .lam _ _ body _ =>
    return body.instantiate1 hDen
  | typeDen =>
    return .app typeDen hDen

/-- `Code.{u} staged typeDen` -/
def mkCodeType (u : Level) (staged typeDen : Expr) : Expr :=
  mkApp2 (.const ``Code [u]) staged typeDen

/-- `Code.mk staged typeDen den gen` -/
def mkCode (u : Level) (staged typeDen den gen : Expr) : Expr :=
  mkApp4 (.const ``Code.mk [u]) staged typeDen den gen

/-- `Code.den' staged typeDen code hDen` -/
def mkCodeDen (u : Level) (staged typeDen code hDen : Expr) : Expr :=
  mkApp4 (.const ``Code.den' [u]) staged typeDen code hDen

/-- `staged.interp = Interp.gen` -/
def mkEqGen (staged : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) (mkStagedInterp staged)
    (mkConst ``Interp.gen)

end

end Thyme.Elab
