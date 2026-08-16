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

structure Code (i : Interp) (α : i = .den → Sort u) where
  den' : (h : i = .den) → α h
  gen : Codegen i := .stub

unif_hint (i : Interp) (h : i = .den) (α : Sort u)
    (code : Code i (fun _ => α))
    (a den : α) where
  code ≟ .mk (fun _ => den) .stub
  den ≟ a
  ⊢ code.den' h ≟ a

namespace Code

def ofGen {i : Interp} (α : i = .den → Sort u)
    (gen : Codegen i)
    (hGen : i = .gen) : Code i α :=
  { gen, den' hDen := nomatch hDen ▸ hGen }

@[ext]
theorem ext' {i : Interp} {α : i = .den → Sort u} {a b : Code i α} :
    a.den' = b.den' → a = b := by
  intro h
  cases a
  cases b
  congr
  apply Subsingleton.elim

@[ext]
theorem funext' {i : Interp}
    {α : i = .den → Sort u} {β : Code i α → Sort v}
    {f g : (a : Code i α) → β a} :
    (∀ a, f ⟨a, .stub⟩ = g ⟨a, .stub⟩) → f = g := by
  intro h
  funext ⟨a, gen⟩
  rw [Codegen.eq_stub gen, h a]

section

abbrev den (self : Code .den α) : α rfl := self.den' rfl

@[ext default + 1]
theorem ext {a b : Code .den α} : a.den = b.den → a = b := by
  intro h
  ext
  exact h

@[ext default + 1]
theorem funext
    {α : Sort u}
    {β : Code .den (fun _ => α) → Sort v}
    {f g : (a : Code .den (fun _ => α)) → β a} :
    (∀ (a : α), f ⟨fun _ => a, .stub⟩ = g ⟨fun _ => a, .stub⟩) → f = g := by
  intro h
  funext ⟨a, gen⟩
  rw [Codegen.eq_stub gen, h (a rfl)]

end

theorem den_heq_of_gen {i : Interp}
    {α β : i = .den → Sort u}
    (hGen : i = .gen)
    (a : (hDen : i = .den) → α hDen)
    (b : (hDen : i = .den) → β hDen) : a ≍ b := by
  have : α = β := by
    funext hDen
    nomatch hGen, hDen
  subst β
  apply heq_of_eq
  funext hDen
  nomatch hGen, hDen

theorem heq_of_gen {i : Interp}
    {α₁ α₂ : i = .den → Sort u}
    (h : i = .gen)
    (a₁ : Code i α₁) (a₂ : Code i α₂) : a₁ ≍ a₂ := by
  have : α₁ = α₂ := eq_of_heq (den_heq_of_gen h α₁ α₂)
  subst α₂
  apply heq_of_eq
  ext1
  apply eq_of_heq
  apply den_heq_of_gen h

end Code

end

end Thyme
