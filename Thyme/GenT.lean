module

public import Thyme.Code
public import Thyme.HDo

open Lean

namespace Thyme

public section

@[expose]
def GenT.Base [s : Staged] (m : Type u → Type v) (ρ : Type u) :=
  s.Gen → m ρ

@[expose]
def GenT [s : Staged] (m : Type u → Type v) (α : Type w) :=
  ∀ ρ, s.Gen → ContT ρ m α

namespace GenT

instance {s : Staged} [Monad m] : Monad (Base m) where
  pure a := fun _ => pure a
  bind x f := fun hGen => bind (x hGen) fun a => f a hGen

instance {s : Staged} : Monad (GenT m) where
  pure a := fun _ _ k => k a
  bind x f := fun ρ hGen k => x ρ hGen fun a => f a ρ hGen k

instance {s : Staged} [Bind m] : MonadLift m (GenT m) where
  monadLift x := fun _ _ k => bind x k

instance {s : Staged} {m : Type u → Type v} [Monad m] :
    MonadLift m (ScopedContT ρ (Base m)) where
  monadLift x := fun _ _ k hGen => bind x fun a => k a hGen

instance {s : Staged} {m : Type u → Type v} [Monad m] :
    HDo (GenT m) (Base m) where
  embed x _ _ _ k hGen := x _ hGen fun a => k a hGen
  project x ρ hGen k := x ρ .normal 0 (fun a _ => k a) hGen

instance {s : Staged} {m : Type u → Type v} [Monad m] :
    MonadLift (GenT m) (ScopedContT ρ (Base m)) where
  monadLift x := fun _ _ k hGen => x _ hGen fun a => k a hGen

def withGen [s : Staged] [Bind m] (f : s.Gen → m α) : GenT m α :=
  fun _ hGen k => bind (f hGen) k

def mkCode {s : Staged} (α : s.Den → Sort u)
    (action : MetaM Expr) : GenT MetaM (Code α) :=
  fun _ hGen k => k <| Code.ofGen α (Codegen.mk fun _ => action) hGen

end GenT

def runGenT [Pure m] (action : ∀ [Staged], GenT m α) : m α :=
  (@action Staged.gen) α Staged.Gen.intro pure

end

end Thyme
