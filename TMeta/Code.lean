module

public import TMeta.Codegen
public import Lean.Meta.Basic

open Lean Meta

namespace TMeta

@[noinline]
def forgeGet (h : False) : Unit → α :=
  fun _ => h.elim

public section

structure Code (α : Sort u) : Sort (max 1 u) where
  mk! ::
  get : Unit → α
  xfc : ExfCodegen

namespace Code

def gen (code : Code α) : Codegen :=
  code.xfc.run

@[expose]
def value (code : Code α) : α :=
  code.get ()

@[expose, macro_inline]
def quote (value : α) (xfc : ExfCodegen := .default) : Code α :=
  mk! (fun _ => value) xfc.squash

unif_hint (code : Code (Sort u)) (α : Sort u) where
  code ≟ quote α
  ⊢ code.get () ≟ α

def forge (h : False) (gen : Codegen) : Code α :=
  mk! (forgeGet h) (.squash fun _ => gen)

@[simp]
theorem value_quote (a : α) (xfc : ExfCodegen := .default) :
    (quote a xfc).value = a :=
  rfl

@[simp]
theorem quote_value (a : Code α) (xfc : ExfCodegen := .default) :
    quote a.value xfc = a := by
  simp [quote]
  congr
  funext _
  nofun

@[ext]
theorem ext {a b : Code α} (h : a.value = b.value) : a = b := by
  rw [← quote_value a, ← quote_value b, h]

@[ext]
theorem funext
    {α : Sort u} {β : Code α → Sort v}
    {f g : (a : Code α) → β a}
    (h : ∀ (a : α), f (quote a) = g (quote a)) :
    f = g := by
  funext x
  rw [← quote_value x, h]

@[coe]
def coe [ToExpr α] (a : α) : Code α :=
  Code.mk! (fun _ => a) (.squash fun _ => pure (toExpr a))

instance [ToExpr α] : Coe α (Code α) where
  coe := coe

@[simp]
theorem coe_eq_quote [ToExpr α] (a : α) :
    coe a = quote a := by
  rfl

end Code

end

end TMeta
