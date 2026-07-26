module

public import TMeta.Codegen
public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

public section

structure Code (α : Sort u) : Sort (max 1 u) where
  /--
  The caller must ensure coherence: the generator produces an
  expression of type `α` that is definitionally equal to `get ()`.
  -/
  mk! ::
  get : Unit → α
  gen : Codegen

namespace Code

@[expose]
def val (code : Code α) : α :=
  code.get ()

@[expose, macro_inline]
def quote (value : α) : Code α :=
  mk! (fun _ => value) .stub

unif_hint (code : Code (Sort u)) (α : Sort u) where
  code ≟ quote α
  ⊢ code.get () ≟ α

@[simp]
theorem val_mk! (a : α) (gen : Codegen) :
    (mk! (fun _ => a) gen).val = a :=
  rfl

@[simp]
theorem val_quote (a : α) :
    (quote a).val = a :=
  rfl

@[simp]
theorem quote_val (a : Code α) :
    quote a.val = a := by
  simp [quote]
  congr
  apply Subsingleton.elim

@[ext]
theorem ext {a b : Code α} (h : a.val = b.val) : a = b := by
  rw [← quote_val a, ← quote_val b, h]

@[ext]
theorem funext
    {α : Sort u} {β : Code α → Sort v}
    {f g : (a : Code α) → β a}
    (h : ∀ (a : α), f (quote a) = g (quote a)) :
    f = g := by
  funext x
  rw [← quote_val x, h]

@[coe]
def coe [ToExpr α] (a : α) : Code α :=
  Code.mk! (fun _ => a) (.mk (pure (toExpr a)))

instance [ToExpr α] : Coe α (Code α) where
  coe := coe

@[simp]
theorem coe_eq_quote [ToExpr α] (a : α) :
    coe a = quote a := by
  rfl

end Code

end

end TMeta
