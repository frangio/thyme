module

import Lean.Elab.Do.Basic
public meta import Lean.Elab.Do.Basic

namespace Thyme

public section

@[expose]
def ContT (ρ : Type u) (m : Type u → Type v) (α : Type w) :=
  (α → m ρ) → m ρ

namespace Scope

structure Spec (m : Type u → Type v) where
  shift : Type u → Type u
  close [Monad m] {ρ : Type u} :
    ContT (shift ρ) m (Unit → m ρ) →
    m ρ

unsafe def impl (m : Type u → Type v) : Scope.Spec m where
  shift _ := PNonScalar
  close _ {ρ} x := do
    let resume ← x fun resume =>
      pure (@unsafeCast (Unit → m ρ) PNonScalar resume)
    (@unsafeCast PNonScalar (Unit → m ρ) resume) ()

@[implemented_by impl]
opaque prim (m : Type u → Type v) : Spec m :=
  ⟨id, fun x => x fun resume => resume ()⟩

def shift (ρ : Type u) (m : Type u → Type v) : Type u :=
  (prim m).shift ρ

def close {ρ : Type u} {m : Type u → Type v} [Monad m]
    (x : ContT (shift ρ m) m (Unit → m ρ)) : m ρ :=
  (prim m).close x

@[expose]
def Answer (ρ : Type u) (m : Type u → Type v) : Nat → Type u
  | 0 => ρ
  | i + 1 => shift (Answer ρ m i) m

end Scope

@[expose]
def ScopedContT (ρ : Type u) (m : Type u → Type v) (α : Type w) :=
  (i : Nat) → ContT (Scope.Answer ρ m i) m α

namespace ScopedContT

protected def bind (x : ScopedContT ρ m α)
    (f : α → ScopedContT ρ m β) : ScopedContT ρ m β :=
  fun i k => x i fun a => f a i k

instance : Monad (ScopedContT ρ m) where
  pure a := fun _ k => k a
  bind := ScopedContT.bind

instance {ρ : Type u} {m : Type u → Type v}
    [Bind m] : MonadLift m (ScopedContT ρ m) where
  monadLift x := fun _ k => Bind.bind x k

def scope {ρ : Type u} {m : Type u → Type v} [Monad m]
    (x : ScopedContT ρ m α) : ScopedContT ρ m α :=
  fun i k =>
    Scope.close fun k' =>
      x (i + 1) fun a => k' (fun () => k a)

instance {ρ : Type u} {m : Type u → Type v}
    [Monad m] [MonadExceptOf ε m] : MonadExceptOf ε (ScopedContT ρ m) where
  throw e := fun _ _ => throwThe ε e
  tryCatch body handler := scope fun i k =>
    tryCatchThe ε (body i k) fun e => handler e i k

end ScopedContT

/--
Defines the internal representation used to elaborate `hdo` blocks
returning values in `m`. Implementations are expected to make `m` a
retract of `∀ ρ, ScopedContT ρ n`.
-/
class HDo (m : Type u → Type v) (n : outParam (Type r → Type s)) where
  embed {α : Type u} : m α → ∀ ρ, ScopedContT ρ n α
  project {α : Type u} : (∀ ρ, ScopedContT ρ n α) → m α

instance (priority := low) {m : Type u → Type v} [Monad m] :
    HDo m m where
  embed x _ _ k := Bind.bind x k
  project x := x _ 0 pure

open Lean.Parser.Term in
syntax:arg (name := hdoStx) ppAllowUngrouped "hdo " doSeq : term

end

open Lean Lean.Meta
open Lean.Elab.Term Lean.Elab.Do

meta def hdoRhoName : Name :=
  addMacroScope `_thyme.hdo `ρ reservedMacroScope

private meta def mkScopedContTFn (ρ n α : Expr) : MetaM Expr := do
  let r ← getDecLevel ρ
  let s ← getDecLevel (.app n ρ)
  let u ← getDecLevel α
  return mkApp2 (.const ``ScopedContT [r, s, u]) ρ n

private meta def hDoOps (n ρ : Expr) : DoOps where
  mkMonadApp α := return .app (← mkScopedContTFn ρ n α) α

  mkPureApp α e := do
    if (← read).deadCode matches .deadSyntactically then
      let m ← mkScopedContTFn ρ n α
      return ← mkFreshExprMVar (some (.app m α))
    let e ← ensureHasType α e
    let m ← mkScopedContTFn ρ n α
    let u ← getDecLevel α
    let v ← getDecLevel (.app m α)
    let instPure ← mkInstMVar (mkApp (.const ``Pure [u, v]) m)
    let instPure ← instantiateMVars instPure
    return mkApp4 (.const ``Pure.pure [u, v]) m instPure α e

  mkBindApp α γ e f := do
    let source ← mkScopedContTFn ρ n α
    let target ← mkScopedContTFn ρ n γ
    let e ← ensureHasType (some (.app source α)) e
    let f ← ensureHasType (← mkArrow α (.app target γ)) f
    let r ← getDecLevel ρ
    let s ← getDecLevel (.app n ρ)
    let u ← getDecLevel α
    let w ← getDecLevel γ
    return mkApp6 (.const ``ScopedContT.bind [r, s, u, w]) ρ n α γ e f

  isPureApp? := DoOps.default.isPureApp?

  splitMonadApp? type := do
    let some (info, resultType) ← DoOps.default.splitMonadApp? type | return none
    return some ({ info with
      cachedPUnit := .const ``Unit []
      cachedPUnitUnit := .const ``Unit.unit []
    }, resultType)

@[term_elab hdoStx]
public meta def elabHDo : TermElab := fun stx expectedType? => do
  let `(hdo $doSeq) := stx | Lean.Elab.throwUnsupportedSyntax
  tryPostponeIfNoneOrMVar expectedType?
  let some expectedType ← expectedType?.filterM (not <$> isMVarApp ·) |
    throwError "invalid `hdo` notation, expected type is not known"
  let ctx ← mkContext (some expectedType)
  let { u, v, m, .. } := ctx.monadInfo
  let β := ctx.doBlockResultType
  let r ← mkFreshLevelMVar
  let s ← mkFreshLevelMVar
  let nType ← mkArrow (.sort r.succ) (.sort s.succ)
  let n ← mkFreshExprMVar nType
  let instHDo ←
    synthInstance (mkApp2 (.const ``HDo [u, v, r, s]) m n)
  let n ← instantiateMVars n
  withLocalDecl hdoRhoName .default (.sort r.succ)
      (kind := .implDetail) fun ρ => do
    let k ← mkScopedContTFn ρ n β
    let kβ := .app k β
    let ops := hDoOps n ρ
    let action ← elabDoWith ops doSeq (some kβ)
    let action ← mkLambdaFVars #[ρ] action
    let result :=
      mkApp5 (.const ``HDo.project [u, v, r, s]) m n instHDo β action
    ensureHasType expectedType result

section

open Lean.Parser.Term
open Lean.PrettyPrinter.Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr
open Lean.TSyntax.Compat

private meta partial def delabHDoElems : DelabM (List Syntax) := do
  let e ← getExpr
  if e.isAppOfArity ``ScopedContT.bind 6 then
    let α := e.getAppArgs[2]!
    let ma ← withAppFn <| withAppArg delab
    withAppArg do
      let .lam _ _ body _ ← getExpr | failure
      withBindingBodyUnusedName fun n => do
        if body.hasLooseBVars then
          prependAndRec `(doElem|let $n:term ← $ma:term)
        else if α.isConstOf ``Unit || α.isConstOf ``PUnit then
          prependAndRec `(doElem|$ma:term)
        else
          prependAndRec `(doElem|let _ ← $ma:term)
  else if e.isLet then
    let .letE n t v b nondep ← getExpr | unreachable!
    let n ← getUnusedName n b
    let stxT ← descend t 0 delab
    let stxV ← descend v 1 delab
    withLetDecl n t v (nondep := nondep) fun fvar =>
      let b := b.instantiate1 fvar
      descend b 2 <|
        if nondep then
          prependAndRec `(doElem|have $(mkIdent n) : $stxT := $stxV)
        else
          prependAndRec `(doElem|let $(mkIdent n) : $stxT := $stxV)
  else
    let stx ← delab
    return [← `(doElem|$stx:term)]
  where
    prependAndRec x := List.cons <$> x <*> delabHDoElems

@[app_delab ScopedContT.bind]
public meta def delabHDo : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``ScopedContT.bind 6
  let elems ← delabHDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(hdo $items:doSeqItem*)

@[app_delab HDo.project]
public meta def delabProjectHDo : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HDo.project 5
  withAppArg do
    let .lam _ _ _ _ ← getExpr | failure
    withBindingBodyUnusedName fun _ => do
      let elems ← delabHDoElems
      let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
      `(hdo $items:doSeqItem*)

end

end Thyme
