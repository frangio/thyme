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
  | .app (.const name _) (mkRawNatLit n) =>
    if name == ``Int.ofNat then
      some (.ofNat n)
    else if name == ``Int.negSucc then
      some (.negSucc n)
    else
      none
  | _ => none

structure ContextEntry where
  instStaged : Staged
  hDen : instStaged.interp = .den

def mkEntry (instStaged hDen : Expr) : Expr :=
  mkApp2 (.const ``ContextEntry.mk []) instStaged hDen

def viewEntry (entry : Expr) : MetaM (Expr × Expr) := do
  let_expr ContextEntry.mk instStaged hDen := entry | throwMalformedContext
  return (instStaged, hDen)

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
  stage : Int
  entered? : Option ContextEntry
  escaped : List ContextEntry

def mkZipper (stage entered escaped : Expr) : Expr :=
  mkApp3 (.const ``ContextZipper.mk []) stage entered escaped

def contextMarkerValue? : Option LocalDecl → Option Expr
  | some (.ldecl _ _ _ type value _ _) =>
    if type.isConstOf ``ContextZipper then some value else none
  | _ => none

def getAmbient : TermElabM (Int × Option Expr × Expr) := do
  let marker? ← (← getLCtx).decls.findSomeRevM? fun decl? =>
    return contextMarkerValue? decl?
  let some zipper := marker?
    | return (0, none, nilEntry)
  let_expr ContextZipper.mk stage entered? escaped := zipper | throwMalformedContext
  let some stage := rawIntLit? stage | throwMalformedContext
  match_expr entered? with
  | Option.none _ => return (stage, none, escaped)
  | Option.some _ entry => return (stage, some entry, escaped)
  | _ => throwMalformedContext

def withMarker (stage : Int) (entered escaped : Expr) (k : TermElabM α) :
    TermElabM α :=
  withLetDecl
    contextMarkerName
    (mkConst ``ContextZipper)
    (mkZipper (mkRawIntLit stage) entered escaped)
    (kind := .implDetail)
    fun _ => k

/-- Enter a denotational context, returning whether it is newly owned, its
staged instance, and the stage of the operator that entered it. -/
public def enterDenContext
    (k : (instStaged hDen : Expr) → TermElabM α) :
    TermElabM (Bool × Expr × Int × α) := do
  let (stage, entered?, escaped) ← getAmbient
  if entered?.isSome then
    throwMultiLevelStagingError
  if let some (entry, escaped) ← listPop? escaped then
    let (instStaged, hDen) ← viewEntry entry
    let result ← withMarker (stage + 1) (someEntry entry) escaped <|
      k instStaged hDen
    return (false, instStaged, stage, result)
  else
    let instStaged ← synthInstance (mkConst ``Staged)
    let interp := mkStagedInterp instStaged
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl hDenName .default (mkEqDen interp)
        (kind := .implDetail) fun hDen => do
      let entry := mkEntry instStaged hDen
      let result ← withMarker (stage + 1) (someEntry entry) escaped <|
        k instStaged hDen
      return (true, instStaged, stage, result)

/-- Escape the current denotational context, invoking `k` with whether this is
a root escape and the stage of the splice operator. -/
public def escapeDenContext
    (k : (isRoot : Bool) → (stage : Int) → (instStaged hDen : Expr) → TermElabM α) :
    TermElabM α := do
  let (stage, entered?, escaped) ← getAmbient
  if let some entry := entered? then
    let (instStaged, hDen) ← viewEntry entry
    withMarker (stage - 1) noneEntry (mkConsEntry entry escaped) <|
      k false stage instStaged hDen
  else
    let instStagedName ← mkFreshUserName instStagedName
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl instStagedName .instImplicit (mkConst ``Staged) fun instStaged => do
      let interp := mkStagedInterp instStaged
      withLocalDecl hDenName .default (mkEqDen interp)
          (kind := .implDetail) fun hDen =>
        let entry := mkEntry instStaged hDen
        withMarker (stage - 1) noneEntry (mkConsEntry entry escaped) <|
          k true stage instStaged hDen

/-- Returns the stage at which the free variable was introduced. -/
public def getFVarStage (fvarId : FVarId) : MetaM Int := do
  let lctx ← getLCtx
  let decl ← fvarId.getDecl
  if h : decl.index < lctx.decls.size then
    for offset in *...decl.index do
      let i := decl.index - (offset + 1)
      let some value := contextMarkerValue? lctx.decls[i] | continue
      let_expr ContextZipper.mk stage _ _ := value | throwMalformedContext
      let some stage := rawIntLit? stage | throwMalformedContext
      return stage
    return 0
  else
    throwError "invalid decl index"

end Thyme.Elab
