module

public import Lean.Meta.Basic

open Lean Meta

namespace Thyme

public section

inductive Interp where
  | den
  | gen
  deriving DecidableEq

def Codegen (i : Interp) := Squash (i = .gen → MetaM Expr)

namespace Codegen

variable {i : Interp}

instance : Subsingleton (Codegen i) :=
  inferInstanceAs (Subsingleton (Squash _))

opaque stub : Codegen i :=
  .mk fun _ => throwError "missing code generator"

private def mkImpl (action : i = .gen → MetaM Expr) : Codegen i :=
  .mk action

@[implemented_by mkImpl]
abbrev mk (action : i = .gen → MetaM Expr) : Codegen i :=
  stub

@[noinline] -- https://github.com/leanprover/lean4/issues/14719
private unsafe def runImpl : Codegen i → i = .gen → MetaM Expr :=
  let α := i = .gen → MetaM Expr
  @unsafeCast (Squash α) α

@[implemented_by runImpl]
opaque run : Codegen i → i = .gen → MetaM Expr

@[simp↓]
theorem mk_eq_stub (action : i = .gen → MetaM Expr) :
    mk action = stub :=
  rfl

theorem eq_stub (gen : Codegen i) : gen = stub := by
  apply Subsingleton.elim

end Codegen

class Staged where
  interp : Interp

instance (priority := low) Staged.den : Staged := ⟨.den⟩

attribute [-instance] Staged.den

structure Code [s : Staged] (α : s.interp = .den → Sort u) where
  den' : (h : s.interp = .den) → α h
  gen : Codegen s.interp := .stub

unif_hint [s : Staged] (h : s.interp = .den) (α : Sort u)
    (code : Code (fun _ => α))
    (a den : α) where
  code ≟ .mk (fun _ => den) .stub
  den ≟ a
  ⊢ code.den' h ≟ a

namespace Code

def ofGen [s : Staged] (α : s.interp = .den → Sort u)
    (gen : Codegen s.interp)
    (hGen : s.interp = .gen) : Code α :=
  { gen, den' hDen := nomatch hDen ▸ hGen }

@[ext]
theorem ext' [s : Staged] {α : s.interp = .den → Sort u} {a b : Code α} :
    a.den' = b.den' → a = b := by
  intro h
  cases a
  cases b
  congr
  apply Subsingleton.elim

@[ext]
theorem funext' [s : Staged]
    {α : s.interp = .den → Sort u} {β : Code α → Sort v}
    {f g : (a : Code α) → β a} :
    (∀ a, f ⟨a, .stub⟩ = g ⟨a, .stub⟩) → f = g := by
  intro h
  funext ⟨a, gen⟩
  rw [Codegen.eq_stub gen, h a]

section

attribute [local instance] Staged.den

abbrev den (self : Code α) : α rfl := self.den' rfl

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
  rw [Codegen.eq_stub gen, h (a rfl)]

end

theorem den_heq_of_gen [s : Staged]
    {α β : s.interp = .den → Sort u}
    (hGen : s.interp = .gen)
    (a : (hDen : s.interp = .den) → α hDen)
    (b : (hDen : s.interp = .den) → β hDen) : a ≍ b := by
  cases s
  have : α = β := by
    funext hDen
    nomatch hGen, hDen
  subst β
  apply heq_of_eq
  funext hDen
  nomatch hGen, hDen

theorem heq_of_gen [s : Staged]
    {α₁ α₂ : s.interp = .den → Sort u}
    (h : s.interp = .gen)
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
