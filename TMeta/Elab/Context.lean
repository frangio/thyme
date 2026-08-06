module

public import Lean.Elab.Term.TermElabM
import TMeta.Elab.Common
import TMeta.Code

namespace TMeta.Elab

open Lean Elab Meta Term

def indexName : Name := `i

def addTMetaScope (name : Name) : Name :=
  addMacroScope `_tmeta name reservedMacroScope

def implicitIndexName : Name :=
  addTMetaScope indexName

def contextMarkerName : Name :=
  addTMetaScope `contextMarker

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
  index : Interpretation
  hDen : Den index

def mkEntry (index hDen : Expr) : Expr :=
  mkApp2 (.const ``ContextEntry.mk []) index hDen

def viewEntry (entry : Expr) : MetaM (Expr × Expr) := do
  let_expr ContextEntry.mk index hDen := entry | throwMalformedContext
  return (index, hDen)

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

def resolveInterpretation (autoBind : Bool) : TermElabM Expr := do
  let autoCtx? := (← read).autoBoundImplicitContext
  let lctx ← getLCtx
  let index? ← autoCtx?.bindM fun autoCtx =>
    autoCtx.boundVariables.findSomeM? fun fvar => do
      let name ← fvar.fvarId!.getUserName
      return if name == implicitIndexName then some fvar else none
  let index? := index?.orElse fun _ =>
    lctx.findFromUserName? implicitIndexName |>.map (·.toExpr)
  if let some index := index? then
    unless ← isDefEq (← inferType index) (mkConst ``Interpretation) do
      throwError "cannot determine an interpretation for staged code"
    return index
  if autoBind && autoCtx?.isSome then
    unless ← autoImplicit.getM do
      throwError "TMeta requires auto-bound implicits to elaborate staged code"
    throwAutoBoundImplicitLocal implicitIndexName
  return mkConst ``Interpretation.den

/-- Enter a denotational context, returning whether it is newly owned, its
interpretation and the stage of the operator that entered it. -/
public def enterDenContext
    (k : (index hDen : Expr) → TermElabM α)
    (autoBind := false) : TermElabM (Bool × Expr × Int × α) := do
  let (stage, entered?, escaped) ← getAmbient
  if entered?.isSome then
    throwError "staging error: multi-level staging is not supported"
  if let some (entry, escaped) ← listPop? escaped then
    let (index, hDen) ← viewEntry entry
    let result ← withMarker (stage + 1) (someEntry entry) escaped <|
      k index hDen
    return (false, index, stage, result)
  else
    let index ← resolveInterpretation autoBind
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl hDenName .instImplicit (mkDenType index) (kind := .implDetail) fun hDen => do
      let entry := mkEntry index hDen
      let result ← withMarker (stage + 1) (someEntry entry) escaped <|
        k index hDen
      return (true, index, stage, result)

/-- Escape the current denotational context, invoking `k` with whether this is
a root escape and the stage of the splice operator. -/
public def escapeDenContext
    (k : (isRoot : Bool) → (stage : Int) → (index hDen : Expr) → TermElabM α) :
    TermElabM α := do
  let (stage, entered?, escaped) ← getAmbient
  if let some entry := entered? then
    let (index, hDen) ← viewEntry entry
    withMarker (stage - 1) noneEntry (mkConsEntry entry escaped) <|
      k false stage index hDen
  else
    let indexName ← mkFreshUserName indexName
    let hDenName ← mkFreshUserName hDenName
    withLocalDecl indexName .default (mkConst ``Interpretation)
        (kind := .implDetail) fun index =>
      withLocalDecl hDenName .instImplicit (mkDenType index)
          (kind := .implDetail) fun hDen =>
        let entry := mkEntry index hDen
        withMarker (stage - 1) noneEntry (mkConsEntry entry escaped) <|
          k true stage index hDen

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

end TMeta.Elab
