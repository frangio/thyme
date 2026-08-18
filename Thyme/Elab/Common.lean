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

/-- `instStaged.interp` -/
def mkStagedInterp (instStaged : Expr) : Expr :=
  .app (mkConst ``Staged.interp) instStaged

/-- `Staged.mk interp` -/
def mkStaged (interp : Expr) : Expr :=
  .app (mkConst ``Staged.mk) interp

/-- `interp = Interp.den` -/
def mkEqDen (interp : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) interp
    (mkConst ``Interp.den)

/-- `fun _ : interp = Interp.den => PUnit.{u}` -/
def mkErasedTypeDen (u : Level) (interp : Expr) : Expr :=
  .lam hDenName (mkEqDen interp) (.const ``PUnit [u]) .default

/-- `typeDen hDen`, exposing a reducible family and its head beta redex. -/
def instantiateTypeDen (typeDen hDen : Expr) : MetaM Expr := do
  match ← whnf typeDen with
  | .lam _ _ body _ =>
    return body.instantiate1 hDen
  | typeDen =>
    return .app typeDen hDen

/-- `Code.{u} interp typeDen` -/
def mkCodeType (u : Level) (interp typeDen : Expr) : Expr :=
  mkApp2 (.const ``Code [u]) interp typeDen

def whnfCodeType? (type : Expr) : MetaM (Option (Level × Expr × Expr)) := do
  let some type ← whnfUntil type ``«Code» | return none
  let mkApp2 (.const _ [u]) interp typeDen := type
    | throwError "malformed Code type"
  return some (u, interp, typeDen)

/-- `Code.mk interp typeDen den gen` -/
def mkCode (u : Level) (interp typeDen den gen : Expr) : Expr :=
  mkApp4 (.const ``Code.mk [u]) interp typeDen den gen

/-- `Code.den' interp typeDen code hDen` -/
def mkCodeDen (u : Level) (interp typeDen code hDen : Expr) : Expr :=
  mkApp4 (.const ``Code.den' [u]) interp typeDen code hDen

/-- `interp = Interp.gen` -/
def mkEqGen (interp : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interp) interp
    (mkConst ``Interp.gen)

end

end Thyme.Elab
