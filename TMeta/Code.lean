module

public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

public section

inductive Interpretation where
  | den
  | gen
  deriving DecidableEq

@[class]
inductive Den : Interpretation → Prop where
  | intro : Den .den

@[default_instance]
instance : Den .den := .intro

namespace Den

def elim : (α : [Den i] → Sort u) → i = .gen → [Den i] → α := nofun

def elimType : i = .gen → [Den i] → Sort u := elim _

theorem heq_of_gen
    {α β : [Den i] → Sort u}
    (hGen : i = .gen)
    (a : [Den i] → α) (b : [Den i] → β) : @a ≍ @b := by
  subst i
  have : @α = @β := by
    funext hDen
    nomatch hDen
  subst β
  apply heq_of_eq
  funext hDen
  nomatch hDen

end Den

def Codegen (i : Interpretation) := Squash (i = .gen → MetaM Expr)

namespace Codegen

instance : Subsingleton (Codegen i) :=
  inferInstanceAs (Subsingleton (Squash _))

opaque stub : Codegen i :=
  .mk fun _ => throwError "missing code generator"

private def mkImpl (action : i = .gen → MetaM Expr) : Codegen i :=
  .mk action

@[implemented_by mkImpl]
abbrev mk (action : i = .gen → MetaM Expr) : Codegen i :=
  stub

private unsafe def runImpl : Codegen i → i = .gen → MetaM Expr :=
  let α := i = .gen → MetaM Expr
  @unsafeCast (Squash α) α

@[implemented_by runImpl]
opaque run : Codegen i → i = .gen → MetaM Expr

end Codegen

structure Code (i : Interpretation) (α : [Den i] → Sort u) where
  den : [Den i] → α
  gen : Codegen i := .stub

unif_hint (i : Interpretation) (h : Den i) (α : Sort u)
    (code : Code i (fun [Den i] => α))
    (a den : α) where
  code ≟ .mk (fun [Den i] => den) .stub
  den ≟ a
  ⊢ @code.den h ≟ a

namespace Code

@[simp↓]
theorem eq_canonical {i : Interpretation} {α : [Den i] → Sort u}
    (den : [Den i] → α) (action : i = .gen → MetaM Expr) :
  mk @den (.mk action) = mk @den .stub := rfl

theorem eq_canonical' {i : Interpretation} {α : [Den i] → Sort u}
    (den : [Den i] → α) (gen : Codegen i) :
    mk @den @gen = mk @den .stub := by
  congr
  apply Subsingleton.elim

@[ext]
theorem ext {a b : Code i @α} (h : @a.den = @b.den) : a = b := by
  cases a
  cases b
  congr
  apply Subsingleton.elim

@[ext]
theorem funext
    {α : [Den i] → Sort u} {β : Code i @α → Sort v}
    {f g : (a : Code i @α) → β a}
    (h : ∀ (a : [Den i] → α), f { den := @a } = g { den := @a }) :
    f = g := by
  funext c
  rcases c with ⟨a⟩
  rw [eq_canonical', h a]

theorem heq_of_gen
    {α₁ α₂ : [Den i] → Sort u}
    (hGen : i = .gen)
    (a₁ : Code i @α₁) (a₂ : Code i @α₂) : a₁ ≍ a₂ := by
  have : @α₁ = @α₂ := eq_of_heq (Den.heq_of_gen hGen @α₁ @α₂)
  subst α₂
  apply heq_of_eq
  subst i
  cases a₁
  cases a₂
  congr
  · funext hDen
    nomatch hDen
  · funext
    apply Subsingleton.elim

end Code

end

end TMeta
