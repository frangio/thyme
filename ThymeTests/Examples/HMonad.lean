module

import all Thyme.HMonad

open Thyme

namespace ThymeTests.Examples.HMonad

def highThenLow (α : Type u) : Id Unit := hdo
  let _ ← pure α
  return ()

def unrelatedUniverses (α : Type u) (β : Type v) : Id Unit := hdo
  let _ ← pure α
  let _ ← pure β
  return ()

def highAfterAction (action : Id Unit) (α : Type u) : Id (Type u) := hdo
  let _ ← action
  return α

#guard_expr Id.run (highAfterAction (pure ()) Nat) =~ Nat

def automaticLift (x : Id Nat) : StateT Nat Id Nat := hdo
  let x ← x
  return x + 1

#guard Id.run ((automaticLift (pure 1)).run 0) == (2, 0)

/--
error: invalid `hdo` notation, expected type is not known
-/
#guard_msgs in
def missingExpectedType := hdo
  let x ← some 1
  return x + 1

abbrev NatOption := Option Nat

def inferredFromAliasedAction : Option Nat := hdo
  let x ← (some 1 : NatOption)
  return x + 1

#guard inferredFromAliasedAction == some 2

/--
warning: This `do` element and its control-flow region are dead code. Consider removing it.
-/
#guard_msgs(warning) in
def mismatchedDeadReturn : Id Nat := hdo
  return 1
  return Type

def mutBinding : Id Nat := hdo
  let mut a := 0
  a := 1
  return a

#guard Id.run mutBinding == 1

def mutActionBinding : Id Nat := hdo
  let mut a ← pure 0
  a := 1
  return a

#guard Id.run mutActionBinding == 1

def forLoop : Id Nat := hdo
  let mut sum := 0
  for i in [0, 1, 2, 3, 4, 5] do
    if i == 1 then continue
    if i == 4 then break
    sum := sum + i
  return sum

#guard Id.run forLoop == 5

def whileLoop : Id Nat := hdo
  let mut i := 0
  while i < 4 do
    i := i + 1
  return i

#guard Id.run whileLoop == 4

def matchBranch (n? : Option Nat) : Id Nat := hdo
  match n? with
  | some 0 => return 1
  | some (n + 1) =>
    let n ← pure n
    return n + 2
  | none => return 0

#guard Id.run (matchBranch none) == 0
#guard Id.run (matchBranch (some 0)) == 1
#guard Id.run (matchBranch (some 3)) == 4

def count [m' : HMonad m] (p : α → Bool) (x : m' α) : m Nat := hdo
  let a ← x
  return if p a then 1 else 0

#guard Id.run (count (fun _ => true) Nat) == 1

end ThymeTests.Examples.HMonad
