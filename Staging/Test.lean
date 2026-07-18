module

import Staging.Code
import Staging.Elab

open Staging

def id₀ (α : Code Type) (a : Code ~α) : Code ~α := a

#guard_expr id₀ `⟨Nat⟩ `⟨0⟩ =~ `⟨0⟩

def map (α β : Code Type) (f : Code ~α → Code ~β) (as : Code (List ~α)) : Code (List ~β) :=
  `⟨(~as).foldr (fun a bs => ~(f `⟨a⟩) :: bs) []⟩

#guard_expr (fun ns => ~(map `⟨Nat⟩ `⟨Nat⟩ (fun n => `⟨~n + 10⟩) `⟨ns⟩)) =~
  (fun (ns : List Nat) => ns.foldr (fun (a : Nat) (bs : List Nat) => (a + 10) :: bs) [])

def exp (n : Nat) (x : Code Nat) : Code Nat :=
    n.repeat (fun y => `⟨~y * ~x⟩) `⟨1⟩

#guard_expr ~(exp 3 `⟨4⟩) =ₛ 1 * 4 * 4 * 4

theorem exp_eq_pow (n : Nat) (x : Code Nat) : (exp n x).splice = x.splice ^ n := by
  unfold exp
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, ih]; rfl

def Vec (n : Nat) (α : Code Type) :=
  n.repeat (fun β => `⟨~α × ~β⟩) `⟨Unit⟩

#guard_expr ~(Vec 3 `⟨Char⟩) =ₛ Char × Char × Char × Unit


def two : Code Nat := `⟨2⟩

#guard_expr ~two =ₛ 2
#guard_expr ~`⟨2⟩ =ₛ 2

def add1 : Code Nat → Code Nat :=
  fun x => `⟨~x + 1⟩

#guard_expr ~(add1 `⟨2⟩) =ₛ 2 + 1

def lam (f : Code Nat → Code Nat) : Code (Nat → Nat) :=
  `⟨fun x => ~(f `⟨x⟩)⟩

#guard_expr ~(lam add1) =ₛ fun x => x + 1

def app : Code (Nat → Nat) → Code Nat → Code Nat :=
  fun f x => `⟨~f ~x⟩

#guard_expr ~(app `⟨fun x => x + 1⟩ `⟨2⟩) =~ 3

def thunk : Code (Nat → Nat) → Code Nat → Code (Unit → Nat) :=
  fun f x => `⟨fun _y => ~f ~x⟩

#guard_expr (~(thunk `⟨fun x => x + 1⟩ `⟨2⟩)) () =~ 3

def nestedLet : Code Nat :=
  `⟨~(let x := `⟨0⟩; `⟨~x⟩)⟩

#guard_expr ~nestedLet =~ 0

def dependentArg (x : Code Nat) (_ : Code (~x = 0)) : Code Nat :=
  x

def dependentQuote : Code Nat :=
  `⟨~(dependentArg `⟨0⟩ `⟨rfl⟩)⟩

/-- error: invalid staging: bound variable `x` is available at stage -1, but is used at stage 0 -/
#guard_msgs in
#check ~(let x := 'c'; `⟨x⟩)
