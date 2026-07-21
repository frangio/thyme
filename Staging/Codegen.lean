module

public import Lean.Meta.Basic

open Lean Meta

namespace Staging

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

def default : ExfCodegen := False.elim

end ExfCodegen

end

end Staging
