module

import Thyme
import ThymeTests.Examples.FoldrFusion
meta import ThymeTests.Guard
meta import ThymeTests.Imported

open Thyme.Prelude
open Lean Meta

def idc [Staged] (α : Code Type) (a : Code ~α) : Code ~α := a

#guard_staged idc `⟨Bool⟩ `⟨true⟩ =~ `⟨true⟩

example [Staged] {α : Code Type} (f : Code ~α → Code Unit) : Code (~α → Unit) :=
  `⟨id (fun x => ~(f `⟨x⟩))⟩

example : (α : Type) → (x : α) → (P : α → Type) → P x → P x :=
  fun (α : Type) (x : α) (P : α → Type) (y : P x) =>
    ~(`⟨y⟩ : Code (P x))

example [Staged] : Code ((α : Type) → α → α) :=
  `⟨fun α x => ~(`⟨x⟩ : Code α)⟩

def map [Staged] (α β : Code Type) (f : Code ~α → Code ~β)
    (as : Code (List ~α)) : Code (List ~β) :=
  `⟨(~as).foldr (fun a bs => ~(f `⟨a⟩) :: bs) []⟩

#guard_staged fun (ns : List Nat) => ~(map `⟨Nat⟩ `⟨Nat⟩ (fun n => `⟨~n + 10⟩) `⟨ns⟩) =ₛ
  fun (ns : List Nat) => ns.foldr (fun (a : Nat) (bs : List Nat) => (a + 10) :: bs) []

def exp [Staged] (n : Nat) (x : Code Nat) : Code Nat :=
  n.repeat (fun y => `⟨~y * ~x⟩) `⟨1⟩

#guard_staged ~(exp 3 `⟨4⟩) =ₛ 1 * 4 * 4 * 4

#guard_staged fun x => ~(exp 3 `⟨x⟩) =ₛ fun x => 1 * x * x * x

theorem exp_eq_pow (n : Nat) (x : Nat) : (exp n `⟨x⟩).den = x ^ n := by
  unfold exp
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, Nat.pow_succ, ih]

def Vec [Staged] (n : Nat) (α : Code Type) :=
  n.repeat (fun β => `⟨~α × ~β⟩) `⟨Unit⟩

#guard_staged ~(Vec 3 `⟨Char⟩) =ₛ Char × Char × Char × Unit

def Vec.map [Staged] {α β : Code Type} (n : Nat) (f : Code ~α → Code ~β)
    (as : Code ~(Vec n α)) : Code ~(Vec n β) :=
  match n with
  | 0 => `⟨()⟩
  | n + 1 => `⟨(~(f `⟨(~as).1⟩), ~(map n f `⟨(~as).2⟩))⟩

#guard_staged fun (ns : ~(Vec 2 `⟨Nat⟩)) =>
    ~(Vec.map 2 (fun n => `⟨~n + 10⟩) `⟨ns⟩) =ₛ
  fun (ns : Nat × Nat × Unit) => (ns.1 + 10, ns.2.1 + 10, ())

section

variable [Staged]
variable {α : Code Type} {β : Code (~α → Type)}

def lift (f : Code ((x : ~α) → ~β x)) :
    (x : Code ~α) → Code (~β ~x) :=
  fun x => `⟨~f ~x⟩

def unlift (f : (x : Code ~α) → Code (~β ~x)) :
    Code ((x : ~α) → ~β x) :=
  `⟨fun x => ~(f `⟨x⟩)⟩

end

section

variable {α : Code Type} {β : Code (~α → Type)}

theorem unlift_lift (f : Code ((x : ~α) → ~β x)) :
    unlift (lift f) = f := by
  ext
  rfl

theorem lift_unlift (f : (x : Code ~α) → Code (~β ~x)) :
    lift (unlift f) = f := by
  ext
  rfl

end

def sharePair [Staged] (x : Code Nat) : Code (Nat × Nat) :=
  `⟨let y := ~x; (y, y)⟩

#guard_staged fun x => ~(sharePair `⟨x + x⟩) =ₛ fun x => let y := x + x; (y, y)

def letCode [Staged] (value : Code Nat) (body : Code Nat → Code Nat) : Code Nat :=
  `⟨let x := ~value; ~(body `⟨x⟩)⟩

#guard_staged
  ~(letCode `⟨1⟩ fun x =>
    letCode `⟨2⟩ fun y =>
    `⟨~x + ~y⟩) =ₛ
  let x := 1
  let y := 2
  x + y

def captures [Staged] (f : Nat → Code Nat → Code Nat → Code Nat) : Code Nat :=
  `⟨let x := 0; ~(let y := 1; `⟨let z := 2; ~(f y `⟨x⟩ `⟨z⟩)⟩)⟩

#guard_staged ~(captures (fun y => cond (y == 1))) =ₛ let  x := 0; let _z := 2; x
#guard_staged ~(captures (fun y => cond (y != 1))) =ₛ let _x := 0; let  z := 2; z

def dependentArg [Staged] (x : Code Nat) (h : Code (~x = 0)) :
    Code { n : Nat // n = 0 } :=
  `⟨⟨~x, ~h⟩⟩

#guard_staged `⟨~(dependentArg `⟨0⟩ `⟨rfl⟩)⟩ =~ `⟨⟨0, rfl⟩⟩

def dependentRootSplice [Staged] (n : Code Nat) : Code (Fin (~n + 1)) :=
  `⟨0⟩

/-- info: 0 -/
#guard_msgs in
#eval ~(dependentRootSplice `⟨1⟩)

/-- error: staging error: variable `x` is not available in the current staging context -/
#guard_msgs in
#check ~(let x := 'c'; `⟨x⟩)

/-- error: staging error: variable `x` is not available in the current staging context -/
#guard_msgs in
def illStagedFVar [Staged] (x : Nat) : Code Nat :=
  `⟨x⟩

def nestedSpliceNatF [Staged] (_ : Nat) : Code Nat := `⟨1⟩

def nestedSpliceNatG [Staged] (_ : Nat) : Code Nat := `⟨2⟩

#guard_staged ~(nestedSpliceNatF ~(nestedSpliceNatG 123)) =ₛ 1

def nestedSpliceFunF [Staged] (_ : Nat → Nat) : Code Nat := `⟨1⟩

def nestedSpliceCodeG [Staged] (_ : Code Nat) : Code Nat := `⟨2⟩

#guard_staged ~(nestedSpliceFunF fun x => ~(nestedSpliceCodeG `⟨x⟩)) =ₛ 1

def nestedSpliceCodeG₂ [Staged] (_ _ : Code Nat) : Code Nat := `⟨2⟩

/-- error: staging error: variable `y` is not available in the current staging context -/
#guard_msgs in
def illStagedNestedSplice (y : Nat) : Nat :=
  ~(nestedSpliceFunF fun x => ~(nestedSpliceCodeG₂ `⟨x⟩ `⟨y⟩))

/-- error: staging error: multi-level staging is not supported -/
#guard_msgs in
def unsupportedNestedCode [Staged] (_ : Code (Code Nat)) : Unit := ()

/-- error: staging error: multi-level staging is not supported -/
#guard_msgs in
def unsupportedNestedQuote [Staged] := `⟨`⟨1⟩⟩

def stagedId [Staged] (α : Code (Sort u)) : Code (~α → ~α) :=
  `⟨fun x => x⟩

#guard_staged ~(`⟨Nat⟩ : Code Type) =ₛ Nat

#guard_staged ~(`⟨Type⟩ : Code (Type 1)) =ₛ Type

def finType [Staged] (n : Code Nat) : Code Type :=
  `⟨Fin ~n⟩

#guard_staged (fun n : Nat => ~(finType `⟨n⟩)) =ₛ fun n : Nat => Fin n

#guard_staged ~(importedSucc `⟨41⟩) =ₛ 41 + 1

/-- error: generated code is not definitionally equal to its denotation
generated:
  41 + 1
denotation:
  (opaqueImportedSucc `⟨41⟩).den

Note: The following definitions were not unfolded because their definition is not exposed:
  opaqueImportedSucc ↦ 4 -/
#guard_msgs in
#check ~(opaqueImportedSucc `⟨41⟩)

/-- Deliberately bypasses staging syntax to exercise the trusted generator boundary. -/
def incoherent [Staged] : Code Nat :=
  Thyme.Code.mk (fun _ => 0) (.mk fun _ => pure (mkNatLit 1))

example : incoherent.den = 0 := rfl

/-- error: generated code is not definitionally equal to its denotation
generated:
  1
denotation:
  incoherent.den -/
#guard_msgs in
#check ~incoherent

/-- warning: declaration may produce an incoherent generator: its elaborated term transports a `Code` value across an equality; ensure that rewrites occur inside quotations

Note: This linter can be disabled with `set_option linter.thyme.codeTransport false` -/
#guard_msgs in
def zero_mul_bad [Staged] (x y : Code Nat) (h : Code (~x = 0 * ~y)) :
    Code (~x = 0) := by
  simpa using h

def zero_mul_good [Staged] (x y : Code Nat) (h : Code (~x = 0 * ~y)) :
    Code (~x = 0) :=
  `⟨by simpa using ~h⟩

theorem useZeroMul (x y : Nat) (h : x = 0 * y) : x = 0 :=
  ~(zero_mul_good `⟨x⟩ `⟨y⟩ `⟨h⟩)

/-- warning: declaration may produce an incoherent generator: its elaborated term transports a `Code` value across an equality; ensure that rewrites occur inside quotations

Note: This linter can be disabled with `set_option linter.thyme.codeTransport false` -/
#guard_msgs in
def substCode [Staged] (n m : Code Nat) (h : n = m)
    (x : Code (Fin ~n)) : Code (Fin ~m) := by
  subst m
  exact x

def CodeAlias [Staged] (n : Code Nat) := Code (Fin ~n)

/-- warning: declaration may produce an incoherent generator: its elaborated term transports a `Code` value across an equality; ensure that rewrites occur inside quotations

Note: This linter can be disabled with `set_option linter.thyme.codeTransport false` -/
#guard_msgs in
def transportCodeAlias [Staged] {n m : Code Nat} (h : n = m)
    (x : CodeAlias n) : CodeAlias m :=
  h ▸ x

/-- warning: declaration may produce an incoherent generator: its elaborated term transports a `Code` value across an equality; ensure that rewrites occur inside quotations

Note: This linter can be disabled with `set_option linter.thyme.codeTransport false` -/
#guard_msgs in
def transportInsideQuote [Staged] {α β : Code Type} (h : α = β)
    (x : Code ~α) : Code ~β :=
  `⟨~(h ▸ x)⟩
