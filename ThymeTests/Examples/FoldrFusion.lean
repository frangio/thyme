module

import Thyme
meta import ThymeTests.Guard

open Thyme

set_option thyme.checkCoherence true

namespace ThymeTests.Examples.FoldrFusion

/-!
List combinators are fused during staging, eliminating intermediate lists.

Adapted from András Kovács's `FoldrFusion.2ltt` example:
https://github.com/AndrasKovacs/staged/blob/9c4e201766/demo/examples/FoldrFusion.2ltt
-/

section

variable [Staged]

def FList (α : Code Type) :=
  (β : Code Type) → (Code ~α → Code ~β → Code ~β) → Code ~β → Code ~β

namespace FList

def nil : FList α :=
  fun _ _ nil => nil

def cons (a : Code ~α) (as : FList α) : FList α :=
  fun β cons nil => cons a (as β cons nil)

def pure (a : Code ~α) : FList α :=
  .cons a .nil

def map (f : Code ~α → Code ~β) (as : FList α) : FList β :=
  fun γ cons nil => as γ (fun a bs => cons (f a) bs) nil

def flatMap (as : FList α) (f : Code ~α → FList β) : FList β :=
  fun γ cons nil => as γ (fun a bs => f a γ cons bs) nil

def filter (f : Code ~α → Code Bool) (as : FList α) : FList α :=
  fun β cons nil =>
    as β (fun a bs => `⟨if ~(f a) then ~(cons a bs) else ~bs⟩) nil

def append (xs ys : FList α) : FList α :=
  fun β cons nil => xs β cons (ys β cons nil)

def ofList (as : Code (List ~α)) : FList α :=
  fun _ cons nil =>
    `⟨(~as).foldr (fun a bs => ~(cons `⟨a⟩ `⟨bs⟩)) ~nil⟩

def toList {α : Code Type} (as : FList α) : Code (List ~α) :=
  as `⟨List ~α⟩ (fun a as => `⟨~a :: ~as⟩) `⟨[]⟩

end FList

end

def succ [Staged] (n : Code Nat) : Code Nat :=
  `⟨Nat.succ ~n⟩

def f1 (xs : List Nat) : List Nat :=
  ~(FList.ofList `⟨xs⟩ |>.map succ |>.map succ |>.map id |>.toList)

#guard_staged f1 =~ fun xs =>
  xs.foldr (fun x xs => Nat.succ (Nat.succ x) :: xs) []

def f2 (xs : List Nat) : List Nat :=
  ~(
    let xs := FList.ofList `⟨xs⟩
    let as := xs.map succ
    let bs := xs.map (succ ∘ succ)
    as.append bs |>.toList
  )

#guard_staged f2 =~ fun xs =>
  xs.foldr (fun x xs => Nat.succ x :: xs)
    (xs.foldr (fun x xs => Nat.succ (Nat.succ x) :: xs) [])

def f3 (xs : List Nat) : List Nat :=
  ~(
    let xs := FList.ofList `⟨xs⟩
    let xys :=
      xs.flatMap fun x =>
        xs.flatMap fun y =>
          .pure `⟨~x + ~y⟩
    xys.map (fun (xy : Code Nat) => `⟨1 + ~xy⟩) |>.toList
  )

#guard_staged f3 =~ fun xs =>
  xs.foldr (fun x xs' =>
    xs.foldr (fun y ys => (1 + (x + y)) :: ys) xs') []

end ThymeTests.Examples.FoldrFusion
