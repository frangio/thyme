module

import Staging.Code
import Staging.Elab

open Staging

def idc (α : Code Type) (a : Code ~α) : Code ~α := a

#guard_expr idc `⟨Bool⟩ `⟨true⟩ =~ `⟨true⟩

def map (α β : Code Type) (f : Code ~α → Code ~β) (as : Code (List ~α)) : Code (List ~β) :=
  `⟨(~as).foldr (fun a bs => ~(f `⟨a⟩) :: bs) []⟩

#guard_expr fun (ns : List Nat) => ~(map `⟨Nat⟩ `⟨Nat⟩ (fun n => `⟨~n + 10⟩) `⟨ns⟩) =ₛ
  fun (ns : List Nat) => ns.foldr (fun (a : Nat) (bs : List Nat) => (a + 10) :: bs) []

def exp (n : Nat) (x : Code Nat) : Code Nat :=
  n.repeat (fun y => `⟨~y * ~x⟩) `⟨1⟩

#guard_expr ~(exp 3 `⟨4⟩) =ₛ 1 * 4 * 4 * 4

#guard_expr fun x => ~(exp 3 `⟨x⟩) =ₛ fun x => 1 * x * x * x

theorem exp_eq_pow (n : Nat) (x : Code Nat) : (exp n x).value = x.value ^ n := by
  unfold exp
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, Nat.pow_succ, ih]

def Vec (n : Nat) (α : Code Type) :=
  n.repeat (fun β => `⟨~α × ~β⟩) `⟨Unit⟩

#guard_expr ~(Vec 3 `⟨Char⟩) =ₛ Char × Char × Char × Unit

def Vec.map {α β : Code Type} (n : Nat) (f : Code ~α → Code ~β) (as : Code ~(Vec n α)) : Code ~(Vec n β) :=
  match n with
  | 0 => `⟨()⟩
  | n + 1 => `⟨(~(f `⟨(~as).1⟩), ~(map n f `⟨(~as).2⟩))⟩

#guard_expr fun (ns : ~(Vec 2 `⟨Nat⟩)) =>
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

#guard_expr fun x => ~(sharePair `⟨x + x⟩) =ₛ fun x => let y := x + x; (y, y)

def dependentArg (x : Code Nat) (h : Code (~x = 0)) : Code { n : Nat // n = 0 } :=
  `⟨⟨~x, ~h⟩⟩

#guard_expr `⟨~(dependentArg `⟨0⟩ `⟨rfl⟩)⟩ =~ `⟨⟨0, rfl⟩⟩

/-- error: invalid staging: bound variable `x` is available at stage -1, but is used at stage 0 -/
#guard_msgs in
#check ~(let x := 'c'; `⟨x⟩)
