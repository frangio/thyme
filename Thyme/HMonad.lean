module

import Lean.Elab.Do.Basic
public meta import Lean.Elab.Do.Basic

namespace Thyme

public section

/--
A heterogeneous bind between different universe instantiations of the
same type family. Instances must ensure that `n` and `m` are
definitionally equal when `u = w`.
-/
class HBind (n : outParam (Type u → Type v)) (m : Type w → Type z) where
  hbind {α : Type u} {β : Type w} : n α → (α → m β) → m β

@[default_instance low]
instance (priority := low) [Bind m] : HBind m m where
  hbind := bind

instance : HBind Id Id where
  hbind x f := f x

instance : HBind Option Option where
  hbind x f := x.bind f

instance : HBind (Except ε) (Except ε) where
  hbind x f := x.bind f

set_option linter.checkUnivs false in
/--
A monad supporting bind across universes.


This is a convenience class that packages `HBind`
-/
class HMonad (m : Type w → Type z) where
  private mk ::
  HBindSource : Type u → Type v
  toMonad : Monad m
  toHBind : HBind HBindSource m

namespace HMonad

/--
Given `hm : HMonad m`, `hm α` refers to `m` instantiated at the
universe of `α`.
-/
instance : CoeFun (HMonad m) fun _ => Type u → Type v where
  coe hm := hm.HBindSource

@[instance_reducible, instance low]
def inst [HBind n m] [Monad m] : HMonad m where
  HBindSource := n
  toMonad := inferInstance
  toHBind := inferInstance

instance (priority := low) [HMonad m] : Monad m :=
  toMonad

instance (priority := low) [hm : HMonad m] : HBind hm m :=
  hm.toHBind

end HMonad

/--
Associates `m` with a type family `km`, indexed by an answer type,
that will be used to elaborate `hdo` blocks. A block with expected
type `m α` is elaborated as `∀ ρ, km ρ α`, then converted to `m α` by
`lower`.

The default uses `ContT m`. A custom family is useful when `m` is a
monad transformer defined using a Codensity-style construction such
as `∀ ρ, ContT n ρ α`, since fixing `ρ` avoids the universe increase
caused by answer-type quantification while elaborating the block.

Implementations must also provide `Monad (km ρ)` and heterogeneous
`HBind` instances for `km ρ`. `MonadLift` instances may be added to
admit actions from other monads.
-/
class HDoMonad
    (m : Type u → Type v)
    (km : outParam ((ρ : Type r) → Type u → Type w)) where
  lower {α : Type u} : (∀ ρ, km ρ α) → m α

@[expose]
def ContT (m : Type u → Type v) (ρ : Type u) (α : Type w) :=
  (α → m ρ) → m ρ

namespace ContT

instance : Monad (ContT m ρ) where
  pure a k := k a
  bind x f k := x fun a => f a k

instance : HBind (ContT m ρ) (ContT m ρ) where
  hbind x f k := x fun a => f a k

instance [HBind n m] : MonadLift n (ContT m ρ) where
  monadLift x k := HBind.hbind x k

instance (priority := low) [Pure m] : HDoMonad m (ContT m) where
  lower x := x _ pure

end ContT

open Lean.Parser.Term in
syntax:arg (name := hdoStx) ppAllowUngrouped "hdo " doSeq : term

end

open Lean Lean.Meta
open Lean.Elab.Term Lean.Elab.Do

meta def hdoRhoName : Name :=
  addMacroScope `_thyme.hdo `ρ reservedMacroScope

private meta def synthHBindSource (info : MonadInfo) (α : Expr) : MetaM Expr := do
  let u ← getDecLevel α
  let v ← mkFreshLevelMVar
  let nType ← mkArrow (.sort u.succ) (.sort v.succ)
  let n ← mkFreshExprMVar nType
  let instType := mkApp2 (.const ``HBind [u, v, info.u, info.v]) n info.m
  discard <| synthInstance instType
  instantiateMVars n

private meta def hDoOps (info : MonadInfo) : DoOps where
  mkMonadApp α := return .app (← synthHBindSource info α) α

  mkPureApp α e := do
    if (← read).deadCode matches .deadSyntactically then
      let m ← synthHBindSource info α
      return ← mkFreshExprMVar (some (.app m α))
    let e ← ensureHasType α e
    let m ← synthHBindSource info α
    let u ← getDecLevel α
    let v ← getDecLevel (.app m α)
    let instPure ← mkInstMVar (mkApp (.const ``Pure [u, v]) m)
    let instPure ← instantiateMVars instPure
    return mkApp4 (.const ``Pure.pure [u, v]) m instPure α e

  mkBindApp α γ e f := do
    let n ← synthHBindSource info α
    let m ← synthHBindSource info γ
    let e ← ensureHasType (some (.app n α)) e
    let f ← ensureHasType (← mkArrow α (.app m γ)) f
    let u ← getDecLevel α
    let v ← getDecLevel (.app n α)
    let w ← getDecLevel γ
    let z ← getDecLevel (.app m γ)
    let inst ← synthInstance (mkApp2 (.const ``HBind [u, v, w, z]) n m)
    return mkApp7 (.const ``HBind.hbind [u, v, w, z]) n m inst α γ e f

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
  let outerInfo@{ u, v, m, .. } := ctx.monadInfo
  let β := ctx.doBlockResultType
  let r ← mkFreshLevelMVar
  let w ← mkFreshLevelMVar
  let kmType ← mkArrow (.sort r.succ)
    (← mkArrow (.sort u.succ) (.sort w.succ))
  let km ← mkFreshExprMVar kmType
  let instHDoMonad ← synthInstance (mkApp2 (.const ``HDoMonad [u, v, r, w]) m km)
  let km ← instantiateMVars km
  withLocalDecl hdoRhoName .default (.sort r.succ)
      (kind := .implDetail) fun ρ => do
    let k := .app km ρ
    let kβ := .app k β
    let kv ← getDecLevel kβ
    let info := { outerInfo with m := k, v := kv }
    let ops := hDoOps info
    let action ← elabDoWith ops doSeq (some kβ)
    let action ← mkLambdaFVars #[ρ] action
    let result :=
      mkApp5 (.const ``HDoMonad.lower [u, v, r, w]) m km instHDoMonad β action
    ensureHasType expectedType result

section

open Lean.Parser.Term
open Lean.PrettyPrinter.Delaborator
open Lean.PrettyPrinter.Delaborator.SubExpr
open Lean.TSyntax.Compat

private meta partial def delabHDoElems : DelabM (List Syntax) := do
  let e ← getExpr
  if e.isAppOfArity ``HBind.hbind 7 then
    let α := e.getAppArgs[3]!
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

@[app_delab HBind.hbind]
public meta def delabHDo : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HBind.hbind 7
  let elems ← delabHDoElems
  let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
  `(hdo $items:doSeqItem*)

@[app_delab HDoMonad.lower]
public meta def delabLowerHDoMonad : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  guard <| (← getExpr).isAppOfArity ``HDoMonad.lower 5
  withAppArg do
    let .lam _ _ _ _ ← getExpr | failure
    withBindingBodyUnusedName fun _ => do
      let elems ← delabHDoElems
      let items ← elems.toArray.mapM (`(doSeqItem|$(·):doElem))
      `(hdo $items:doSeqItem*)

end

end Thyme
