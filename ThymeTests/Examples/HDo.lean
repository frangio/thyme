module

import all Thyme.HDo
import all Thyme.GenT

open Thyme

namespace ThymeTests.Examples.HDo

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

def incrementState : StateM Nat Nat := hdo
  let n ← get
  set (n + 1)
  return n

#guard Id.run (incrementState 3) == (3, 4)

def stateOverExcept (fail : Bool) : StateT Nat (Except String) Nat := hdo
  let n ← get
  if fail then
    let _ ← (throw "failure" : Except String Unit)
  set (n + 1)
  return n

#guard match (stateOverExcept false).run 3 with
  | .ok (3, 4) => true
  | _ => false

#guard match (stateOverExcept true).run 3 with
  | .error "failure" => true
  | _ => false

def recover [Pure m] [MonadExceptOf String m] (x : m Nat) : m Nat :=
  tryCatch x fun _ => pure 2

def dynamicExceptionScope : Except String Nat := hdo
  let n ← recover (pure 1)
  if n = 1 then
    throw "outer continuation"
  else
    return n

#guard dynamicExceptionScope matches .error "outer continuation"

abbrev TwoExcept := Except (Sum String Nat)

instance : MonadExceptOf String TwoExcept where
  throw e := .error (.inl e)
  tryCatch x handler := match x with
    | .error (.inl e) => handler e
    | .error (.inr e) => .error (.inr e)
    | .ok a => .ok a

instance : MonadExceptOf Nat TwoExcept where
  throw e := .error (.inr e)
  tryCatch x handler := match x with
    | .error (.inl e) => .error (.inl e)
    | .error (.inr e) => handler e
    | .ok a => .ok a

def twoExceptionKinds (useNat : Bool) : TwoExcept Nat := hdo
  try
    let n ←
      try
        if useNat then
          throwThe Nat 7
        else
          throwThe String "abc"
      catch e : String =>
        pure e.length
    pure n
  catch n : Nat =>
    pure (n + 1)

#guard twoExceptionKinds false matches .ok 3
#guard twoExceptionKinds true matches .ok 8

def LargeExcept (α : Type) :=
  ULift.{1, 0} (Except String α)

instance : Monad LargeExcept where
  pure a := .up (.ok a)
  bind x f := .up <| x.down.bind fun a => (f a).down

instance : MonadExceptOf String LargeExcept where
  throw e := .up (.error e)
  tryCatch x handler := .up <| match x.down with
    | .ok a => .ok a
    | .error e => (handler e).down

def nestedExceptionScope : LargeExcept Nat := hdo
  try
    let n ←
      try
        pure 1
      catch _ =>
        pure 2
    if n = 1 then
      throw "between"
    else
      pure n
  catch _ =>
    pure 3

#guard nestedExceptionScope.down matches .ok 3

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

meta def genTMeta [Staged] : GenT Lean.MetaM Lean.Expr := hdo
  Lean.logInfo "hdo"
  Lean.Meta.mkFreshExprMVar none

end ThymeTests.Examples.HDo
