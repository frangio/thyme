module

public import Lean.Meta.Basic

open Lean Meta

namespace Thyme

public section

class Staged where
  private mk ::
  Den : Prop

namespace Staged

def Gen [s : Staged] : Prop := ¬s.Den

@[instance_reducible, instance low]
def den : Staged := ⟨True⟩

@[instance_reducible]
def gen : Staged := ⟨False⟩

theorem Den.intro : den.Den := True.intro

theorem Gen.intro : gen.Gen := False.elim

end Staged

-- Disable instance locally to avoid accidental use.
attribute [-instance] Staged.den

def Codegen [s : Staged] := Squash (s.Gen → MetaM Expr)

namespace Codegen

instance {s : Staged} : Subsingleton Codegen :=
  inferInstanceAs (Subsingleton (Squash _))

opaque stub [s : Staged] : Codegen :=
  .mk fun _ => throwError "missing code generator"

private def mkImpl [s : Staged] (action : s.Gen → MetaM Expr) : Codegen :=
  .mk action

@[implemented_by mkImpl]
abbrev mk [s : Staged] (action : s.Gen → MetaM Expr) : Codegen :=
  stub

@[noinline] -- https://github.com/leanprover/lean4/issues/14719
private unsafe def runImpl {s : Staged} : Codegen → s.Gen → MetaM Expr :=
  let α := s.Gen → MetaM Expr
  @unsafeCast (Squash α) α

@[implemented_by runImpl]
opaque run {s : Staged} : Codegen → s.Gen → MetaM Expr

@[simp↓]
theorem mk_eq_stub {s : Staged} (action : s.Gen → MetaM Expr) :
    mk action = stub :=
  rfl

theorem eq_stub {s : Staged} (gen : Codegen) : gen = stub := by
  apply Subsingleton.elim

end Codegen

structure Code [s : Staged] (α : s.Den → Sort u) where
  den' : (h : s.Den) → α h
  gen : Codegen := .stub

unif_hint [s : Staged] (h : s.Den) (α : Sort u)
    (code : Code (fun _ => α))
    (a den : α) where
  code ≟ .mk (fun _ => den) .stub
  den ≟ a
  ⊢ code.den' h ≟ a

namespace Code

def ofGen {s : Staged} (α : s.Den → Sort u)
    (gen : Codegen)
    (hGen : s.Gen) : Code α :=
  { gen, den' hDen := nomatch hGen, hDen }

@[ext]
theorem ext' {s : Staged} {α : s.Den → Sort u} {a b : Code α} :
    a.den' = b.den' → a = b := by
  intro h
  cases a
  cases b
  congr
  apply Subsingleton.elim

@[ext]
theorem funext' {s : Staged}
    {α : s.Den → Sort u} {β : Code α → Sort v}
    {f g : (a : Code α) → β a} :
    (∀ a, f ⟨a, .stub⟩ = g ⟨a, .stub⟩) → f = g := by
  intro h
  funext ⟨a, gen⟩
  rw [Codegen.eq_stub gen, h a]

section

attribute [local instance] Staged.den

abbrev den (self : Code α) : α .intro :=
  self.den' .intro

@[ext default + 1]
theorem ext {a b : Code α} : a.den = b.den → a = b := by
  intro h
  ext
  exact h

@[ext default + 1]
theorem funext
    {α : Sort u}
    {β : Code (fun _ => α) → Sort v}
    {f g : (a : Code (fun _ => α)) → β a} :
    (∀ (a : α), f ⟨fun _ => a, .stub⟩ = g ⟨fun _ => a, .stub⟩) → f = g := by
  intro h
  funext ⟨a, gen⟩
  rw [Codegen.eq_stub gen, h (a .intro)]

end

theorem den_heq_of_gen {s : Staged}
    {α β : s.Den → Sort u}
    (hGen : s.Gen)
    (a : (hDen : s.Den) → α hDen)
    (b : (hDen : s.Den) → β hDen) : a ≍ b := by
  have : α = β := by
    funext hDen
    nomatch hGen, hDen
  subst β
  apply heq_of_eq
  funext hDen
  nomatch hGen, hDen

theorem heq_of_gen {s : Staged}
    {α₁ α₂ : s.Den → Sort u}
    (h : s.Gen)
    (a₁ : Code α₁) (a₂ : Code α₂) : a₁ ≍ a₂ := by
  have : α₁ = α₂ := eq_of_heq (den_heq_of_gen h α₁ α₂)
  subst α₂
  apply heq_of_eq
  ext1
  apply eq_of_heq
  apply den_heq_of_gen h

end Code

end

end Thyme
