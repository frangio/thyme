module

public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

public section

abbrev Codegen := MetaM Expr

abbrev ExfCodegen := False → Codegen

namespace ExfCodegen

private unsafe def runImpl (xfc : ExfCodegen) : Codegen :=
  xfc lcProof

@[implemented_by runImpl]
opaque run (xfc : ExfCodegen) : Codegen

private def squashImpl (xfc : ExfCodegen) : ExfCodegen :=
  xfc

@[expose, implemented_by squashImpl]
def squash (xfc : ExfCodegen) : ExfCodegen :=
  False.elim

def default : ExfCodegen :=
  .squash fun _ => throwError "missing code generator"

end ExfCodegen

end

end TMeta
