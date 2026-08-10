module

public import Lean.Elab.Term.TermElabM
import Thyme.Elab.Common
import Thyme.Code

namespace Thyme.Elab

open Lean Elab Meta Term

def addThymeScope (name : Name) : Name :=
  addMacroScope `_thyme name reservedMacroScope

def contextMarkerName : Name :=
  addThymeScope `contextMarker

def throwMalformedContext [Monad m] [MonadError m] : m α :=
  throwError "malformed staging context"

public def mkRawIntLit : Int → Expr
  | .ofNat n => .app (.const ``Int.ofNat []) (mkRawNatLit n)
  | .negSucc n => .app (.const ``Int.negSucc []) (mkRawNatLit n)

public def rawIntLit? : Expr → Option Int
  | .app (.const ``Int.ofNat []) (mkRawNatLit n) => some (.ofNat n)
  | .app (.const ``Int.negSucc []) (mkRawNatLit n) => some (.negSucc n)
  | _ => none

structure ContextEntry where
  staged : Staged
  hDen : staged.interp = .den

def mkEntry (staged hDen : Expr) : Expr :=
  mkApp2 (.const ``ContextEntry.mk []) staged hDen

def viewEntry (entry : Expr) : MetaM (Expr × Expr) := do
  let_expr ContextEntry.mk staged hDen := entry | throwMalformedContext
  return (staged, hDen)

def nilEntry : Expr :=
  .app (.const ``List.nil [.zero]) (.const ``ContextEntry [])

def noneEntry : Expr :=
  .app (.const ``Option.none [.zero]) (.const ``ContextEntry [])

def someEntry (entry : Expr) : Expr :=
  mkApp2 (.const ``Option.some [.zero]) (.const ``ContextEntry []) entry

def mkConsEntry (entry tail : Expr) : Expr :=
  mkApp3 (.const ``List.cons [.zero]) (.const ``ContextEntry []) entry tail

def listPop? (list : Expr) : MetaM (Option (Expr × Expr)) := do
  match_expr list with
  | List.nil _ =>
    return none
  | List.cons _ head tail =>
    return some (head, tail)
  | _ => throwMalformedContext

structure ContextZipper where
  level : Int
  entered? : Option ContextEntry
  escaped : List ContextEntry

def mkZipper (level entered escaped : Expr) : Expr :=
  mkApp3 (.const ``ContextZipper.mk []) level entered escaped

def contextMarkerValue? : Option LocalDecl → Option Expr
  | some (.ldecl _ _ _ type value _ _) =>
    if type.isConstOf ``ContextZipper then some value else none
  | _ => none

def getAmbient : TermElabM (Int × Option Expr × Expr) := do
  let marker? ← (← getLCtx).decls.findSomeRevM? fun decl? =>
    return contextMarkerValue? decl?
  let some zipper := marker?
    | return (0, none, nilEntry)
  let_expr ContextZipper.mk level entered? escaped := zipper | throwMalformedContext
  let some level := rawIntLit? level | throwMalformedContext
  match_expr entered? with
  | Option.none _ => return (level, none, escaped)
  | Option.some _ entry => return (level, some entry, escaped)
  | _ => throwMalformedContext

def withMarker (level : Int) (entered escaped : Expr) (k : TermElabM α) :
    TermElabM α :=
  withLetDecl
    contextMarkerName
    (mkConst ``ContextZipper)
    (mkZipper (mkRawIntLit level) entered escaped)
    (kind := .implDetail)
    fun _ => k

/-- Enter a denotational context, returning whether it is newly owned, its
staged instance, and the level of the operator that entered it. -/
public def enterDenContext
    (k : (staged hDen : Expr) → TermElabM α) :
    TermElabM (Bool × Expr × Int × α) := do
  let (level, entered?, escaped) ← getAmbient
  if entered?.isSome then
    throwMultiLevelStagingError
  if let some (entry, escaped) ← listPop? escaped then
    let (staged, hDen) ← viewEntry entry
    let result ← withMarker (level + 1) (someEntry entry) escaped <|
      k staged hDen
    return (false, staged, level, result)
  else
    let staged ← synthInstance (mkConst ``Staged)
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl hDenName .default (mkEqDen staged) (kind := .implDetail) fun hDen => do
      let entry := mkEntry staged hDen
      let result ← withMarker (level + 1) (someEntry entry) escaped <|
        k staged hDen
      return (true, staged, level, result)

/-- Escape the current denotational context, invoking `k` with whether this is
a root escape and the level of the splice operator. -/
public def escapeDenContext
    (k : (isRoot : Bool) → (level : Int) → (staged hDen : Expr) → TermElabM α) :
    TermElabM α := do
  let (level, entered?, escaped) ← getAmbient
  if let some entry := entered? then
    let (staged, hDen) ← viewEntry entry
    withMarker (level - 1) noneEntry (mkConsEntry entry escaped) <|
      k false level staged hDen
  else
    let stagedName ← mkFreshUserName stagedName
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl stagedName .instImplicit (mkConst ``Staged) fun staged =>
      withLocalDecl hDenName .default (mkEqDen staged)
          (kind := .implDetail) fun hDen =>
        let entry := mkEntry staged hDen
        withMarker (level - 1) noneEntry (mkConsEntry entry escaped) <|
          k true level staged hDen

/-- Returns the staging level at which the free variable was introduced. -/
public def getFVarLevel (fvarId : FVarId) : MetaM Int := do
  let lctx ← getLCtx
  let decl ← fvarId.getDecl
  if h : decl.index < lctx.decls.size then
    for offset in *...decl.index do
      let i := decl.index - (offset + 1)
      let some value := contextMarkerValue? lctx.decls[i] | continue
      let_expr ContextZipper.mk level _ _ := value | throwMalformedContext
      let some level := rawIntLit? level | throwMalformedContext
      return level
    return 0
  else
    throwError "invalid decl index"

end Thyme.Elab
