module

public import Lean.Meta.Basic
import TMeta.Code

open Lean Meta

namespace TMeta.Elab

public section

def hDenName : Name := `hDen
def hGenName : Name := `hGen

/-- `Den index` -/
def mkDenType (index : Expr) : Expr :=
  .app (mkConst ``Den) index

/-- `[Den index] → bodyType` -/
def mkForallDen (index bodyType : Expr) : Expr :=
  .forallE hDenName (mkDenType index) bodyType .instImplicit

/-- `Den.elimType index hGen` -/
def mkDenElimType (u : Level) (index hGen : Expr) : Expr :=
  mkApp2 (.const ``Den.elimType [u]) index hGen

/-- `typeDen hDen`, exposing a reducible family and its head beta redex. -/
def instantiateTypeDen (typeDen hDen : Expr) : MetaM Expr := do
  return .headBeta (.app (← whnf typeDen) hDen)

/-- `Code.{u} index typeDen` -/
def mkCodeType (u : Level) (index typeDen : Expr) : Expr :=
  mkApp2 (.const ``Code [u]) index typeDen

/-- `Code.mk index typeDen den gen` -/
def mkCode (u : Level) (index typeDen den gen : Expr) : Expr :=
  mkApp4 (.const ``Code.mk [u]) index typeDen den gen

/-- `Code.den index typeDen code hDen` -/
def mkCodeDen (u : Level) (index typeDen code hDen : Expr) : Expr :=
  mkApp4 (.const ``Code.den [u]) index typeDen code hDen

/-- `index = Interpretation.gen` -/
def mkEqGen (index : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [.one]) (mkConst ``Interpretation) index
    (mkConst ``Interpretation.gen)

end

end TMeta.Elab
