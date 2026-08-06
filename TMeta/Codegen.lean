module

public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

public section

def Codegen := Squash (MetaM Expr)

namespace Codegen

opaque stubAction : MetaM Expr :=
  throwError "missing code generator"

opaque stub : Codegen :=
  .mk stubAction

instance : Inhabited Codegen :=
  ⟨stub⟩

instance : Subsingleton Codegen :=
  inferInstanceAs (Subsingleton (Squash (MetaM Expr)))

private def mkImpl (action : MetaM Expr) : Codegen :=
  .mk action

@[implemented_by mkImpl]
abbrev mk (action : MetaM Expr) : Codegen :=
  stub

private unsafe def runImpl (gen : Codegen) : MetaM Expr :=
  @unsafeCast (Squash (MetaM Expr)) (MetaM Expr) gen

@[implemented_by runImpl]
opaque run (gen : Codegen) : MetaM Expr

end Codegen

end

end TMeta
