module

public import Thyme.Code
public import Thyme.Elab
public import Thyme.GenT

open Lean
open Thyme.Prelude

namespace Thyme.Meta

public section

def mkFreshExprMVar [Staged] (type : Code (Sort u)) :
    GenT MetaM (Code ~type × MVarId) := hdo
  let typeExpr ← GenT.withGen type.gen.run
  let expr ← Lean.Meta.mkFreshExprMVar (some typeExpr)
  let code ← GenT.mkCode type.den' (pure expr)
  return (code, expr.mvarId!)

end

end Thyme.Meta
