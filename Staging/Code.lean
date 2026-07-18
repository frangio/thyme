module

public import Staging.Codegen
public import Lean.Meta.Basic

open Lean Meta

namespace Staging

@[noinline]
def elimThunk (h : False) : Unit → α :=
  fun _ => h.elim

public section

inductive Code (α : Sort u) : Sort (max 1 u) where
  | mk (get : Unit → α) (xfc : ExfCodegen)

namespace Code

def gen : Code α → Codegen
  | .mk _ xfc => xfc.run

@[expose]
def splice : Code α → α
  | .mk get _ => get ()

@[expose, macro_inline]
def quote (value : α) (xfc : ExfCodegen := False.elim) : Code α :=
  mk (fun _ => value) xfc.squash

def forge (h : False) (gen : Codegen) : Code α :=
  mk (elimThunk h) (.squash fun _ => gen)

@[simp]
theorem splice_quote (a : α) :
    (quote a).splice = a :=
  rfl

@[simp]
theorem quote_splice (a : Code α) (xfc : ExfCodegen):
    quote a.splice xfc = a := by
  simp [quote]
  congr
  funext _
  nofun

end Code

end

end Staging
