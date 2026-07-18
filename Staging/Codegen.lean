module

public import Lean.Meta.Basic
public import Lean.Meta.Eval

open Lean Meta

namespace Staging

public section

abbrev Codegen := MetaM Expr

private unsafe def evalCodegenImpl (gen : Expr) : Codegen := do
  let result ← evalExpr Codegen (mkConst ``Codegen) gen
  result

@[implemented_by evalCodegenImpl]
opaque evalCodegen (gen : Expr) : Codegen

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

end ExfCodegen

end

end Staging
