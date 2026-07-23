module

import TMeta
public meta import TMetaTests.Imported
public meta import Lean.Elab.Tactic.Guard

open TMeta
open Lean Elab Command Term Meta
open Lean.Parser Lean.Parser.Tactic Lean.Parser.Command
open Lean.Elab.Tactic.GuardExpr

set_option tmeta.checkCoherence true

public section

/-- Variant of `#guard_expr` that prints elaborated terms on error. -/
elab "#guard_staged " r:term:51 eq:equal p:term : command =>
  Lean.Elab.Command.runTermElabM fun _ => Term.withoutErrToSorry do
    let some mk := equal.toMatchKind eq | throwUnsupportedSyntax
    let r ← elabTerm r none
    let p ← elabTerm p none
    _ ← isDefEqGuarded (← inferType r) (← inferType p)
    synthesizeSyntheticMVarsNoPostponing
    let r ← instantiateMVars r
    let p ← instantiateMVars p
    let res ← mk.isEq r p
    unless res do throwError m!"Elaborated term:{indentExpr r}\n\
      is not {mk.toStringDescr} expected term:{indentExpr p}"

end

def idc (α : Code Type) (a : Code ~α) : Code ~α := a

#guard_staged idc `⟨Bool⟩ `⟨true⟩ =~ `⟨true⟩

example {α : Code Type} (f : Code ~α → Code Unit) : Code (~α → Unit) :=
  `⟨id (fun x => ~(f `⟨x⟩))⟩

example : (α : Type) → (x : α) → (P : α → Type) → P x → P x :=
  fun (α : Type) (x : α) (P : α → Type) (y : P x) =>
    ~(`⟨y⟩ : Code (P x))

example : Code ((α : Type) → α → α) :=
  `⟨fun α x => ~(`⟨x⟩ : Code α)⟩

def map (α β : Code Type) (f : Code ~α → Code ~β) (as : Code (List ~α)) : Code (List ~β) :=
  `⟨(~as).foldr (fun a bs => ~(f `⟨a⟩) :: bs) []⟩

#guard_staged fun (ns : List Nat) => ~(map `⟨Nat⟩ `⟨Nat⟩ (fun n => `⟨~n + 10⟩) `⟨ns⟩) =ₛ
  fun (ns : List Nat) => ns.foldr (fun (a : Nat) (bs : List Nat) => (a + 10) :: bs) []

def exp (n : Nat) (x : Code Nat) : Code Nat :=
  n.repeat (fun y => `⟨~y * ~x⟩) `⟨1⟩

#guard_staged ~(exp 3 `⟨4⟩) =ₛ 1 * 4 * 4 * 4

#guard_staged fun x => ~(exp 3 `⟨x⟩) =ₛ fun x => 1 * x * x * x

theorem exp_eq_pow (n : Nat) (x : Code Nat) : (exp n x).val = x.val ^ n := by
  unfold exp
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, Nat.pow_succ, ih]

def Vec (n : Nat) (α : Code Type) :=
  n.repeat (fun β => `⟨~α × ~β⟩) `⟨Unit⟩

#guard_staged ~(Vec 3 `⟨Char⟩) =ₛ Char × Char × Char × Unit

def Vec.map {α β : Code Type} (n : Nat) (f : Code ~α → Code ~β) (as : Code ~(Vec n α)) : Code ~(Vec n β) :=
  match n with
  | 0 => `⟨()⟩
  | n + 1 => `⟨(~(f `⟨(~as).1⟩), ~(map n f `⟨(~as).2⟩))⟩

#guard_staged fun (ns : ~(Vec 2 `⟨Nat⟩)) =>
    ~(Vec.map 2 (fun n => `⟨~n + 10⟩) `⟨ns⟩) =ₛ
  fun (ns : Nat × Nat × Unit) => (ns.1 + 10, ns.2.1 + 10, ())

section

variable {α : Code Type} {β : Code (~α → Type)}

def lift (f : Code ((x : ~α) → ~β x)) :
    (x : Code ~α) → Code (~β ~x) :=
  fun x => `⟨~f ~x⟩

def unlift (f : (x : Code ~α) → Code (~β ~x)) :
    Code ((x : ~α) → ~β x) :=
  `⟨fun x => ~(f `⟨x⟩)⟩

theorem unlift_lift (f : Code ((x : ~α) → ~β x)) :
    unlift (lift f) = f := by
  ext
  rfl

theorem lift_unlift (f : (x : Code ~α) → Code (~β ~x)) :
    lift (unlift f) = f := by
  ext
  rfl

end

def sharePair (x : Code Nat) : Code (Nat × Nat) :=
  `⟨let y := ~x; (y, y)⟩

#guard_staged fun x => ~(sharePair `⟨x + x⟩) =ₛ fun x => let y := x + x; (y, y)

def dependentArg (x : Code Nat) (h : Code (~x = 0)) : Code { n : Nat // n = 0 } :=
  `⟨⟨~x, ~h⟩⟩

#guard_staged `⟨~(dependentArg `⟨0⟩ `⟨rfl⟩)⟩ =~ `⟨⟨0, rfl⟩⟩

/-- error: stage mismatch: bound variable `x` is available at stage -1, but is used at stage 0 -/
#guard_msgs in
#check ~(let x := 'c'; `⟨x⟩)

variable (n : Nat) in
#check_simp (`⟨~↑n⟩ : Code Nat).val ~> n

#guard_staged ~(~(`⟨`⟨1⟩⟩ : Code (Code Nat))) =ₛ 1

def nestedValue (x : Code (Code Nat)) : Code (Code Nat) :=
  `⟨`⟨~~x⟩⟩

#guard_staged ~(nestedValue `⟨`⟨1⟩⟩) =~ `⟨1⟩

def rawQuote (n : Nat) : Code Nat := .quote n
/-- error: missing code generator -/
#guard_msgs in
#check ~(rawQuote 1 : Code Nat)

#guard_staged ~(importedSucc `⟨41⟩) =ₛ 41 + 1

/-- error: generated code is not definitionally equal to its denotation
generated:
  41 + 1
denotation:
  (opaqueImportedSucc («Code».quote 41)).val

Note: The following definitions were not unfolded because their definition is not exposed:
  opaqueImportedSucc ↦ 1 -/
#guard_msgs in
#check ~(opaqueImportedSucc `⟨41⟩)
