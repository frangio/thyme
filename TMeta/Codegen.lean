module

public import TMeta.Discharge
public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

public section

def Codegen := Squash (MetaM Expr)

namespace Codegen

opaque stub : Codegen :=
  .mk (throwError "missing code generator")

instance : Inhabited Codegen :=
  ⟨stub⟩

instance : Subsingleton Codegen :=
  inferInstanceAs (Subsingleton (Squash (MetaM Expr)))

private def mkImpl (action : MetaM Expr) : Codegen :=
  .mk action

@[expose, implemented_by mkImpl]
def mk (action : MetaM Expr) : Codegen :=
  stub

@[always_inline]
private def absImpl {α : Sort u} (k : (Unit → α) → Codegen) : Codegen :=
  discharge! k (msg :=
    "TMeta: internal error: a code generator observed an erased variable")

@[expose, implemented_by absImpl]
def abs {α : Sort u} (k : (Unit → α) → Codegen) : Codegen :=
  stub

private unsafe def runImpl (gen : Codegen) : MetaM Expr :=
  @unsafeCast (Squash (MetaM Expr)) (MetaM Expr) gen

@[implemented_by runImpl]
opaque run (gen : Codegen) : MetaM Expr

end Codegen

end

end TMeta
