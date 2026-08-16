module

public import Lean.Meta.Basic
import Thyme.Code
import Thyme.Elab.Context

open Lean Meta Elab

namespace Thyme.Elab

structure CheckState where
  binders : Array Name
  segmentStarts : Array Nat
  segmentStages : Array Int
  segmentSizes : segmentStarts.size = segmentStages.size

structure CheckContext where
  stagedFVarId? : Option FVarId

abbrev CheckM := ReaderT CheckContext (StateT CheckState MetaM)

def pushBinder (name : Name) : CheckM PUnit :=
  modify fun s => { s with binders := s.binders.push name }

def popBinder : CheckM PUnit :=
  modify fun s => { s with binders := s.binders.pop }

def pushSegment (stage : Int) : CheckM PUnit :=
  modify fun s => {
    s with
    segmentStarts := s.segmentStarts.push s.binders.size
    segmentStages := s.segmentStages.push stage
    segmentSizes := by simp [s.segmentSizes]
  }

def popSegment : CheckM PUnit :=
  modify fun s => {
    s with
    segmentStarts := s.segmentStarts.pop
    segmentStages := s.segmentStages.pop
    segmentSizes := by simp [s.segmentSizes]
  }

def currentStage : CheckM Int :=
  return (← get).segmentStages.back!

def binderIndex (deBruijnIndex : Nat) : CheckM Nat := do
  let numBinders := (← get).binders.size
  unless deBruijnIndex < numBinders do
    throwError "unexpected loose bound variable #{deBruijnIndex}"
  return numBinders - (deBruijnIndex + 1)

def binderName (deBruijnIndex : Nat) : CheckM Name := do
  let index ← binderIndex deBruijnIndex
  return (← get).binders[index]!

def binderStage (deBruijnIndex : Nat) : CheckM Int := do
  let index ← binderIndex deBruijnIndex
  let { segmentStarts, segmentStages, segmentSizes, .. } ← get
  for h : offset in *...segmentStarts.size do
    let i := segmentStarts.size - (offset + 1)
    if segmentStarts[i] ≤ index then
      return segmentStages[i]
  unreachable!

inductive AppState
  | regular
  | code0
  | code1
  | code2
  | mk0
  | mk1
  | mk2
  | mk3
  | mk4
  | den0
  | den1
  | den2
  | den3
  | den4
  deriving Inhabited

namespace AppState

def isUnsaturatedOp (state : AppState) : Bool :=
  state matches
    .code0 | .code1 |
    .mk0 | .mk1 | .mk2 | .mk3 |
    .den0 | .den1 | .den2 | .den3

def next : AppState → AppState
  | .regular => .regular
  | .code0 => .code1
  | .code1 => .code2
  | .code2 => unreachable!
  | .mk0 => .mk1
  | .mk1 => .mk2
  | .mk2 => .mk3
  | .mk3 => .mk4
  | .mk4 => unreachable!
  | .den0 => .den1
  | .den1 => .den2
  | .den2 => .den3
  | .den3 => .den4
  | .den4 => .regular

def opName : AppState → Name
  | .regular => unreachable!
  | .code0 | .code1 | .code2 => ``Code
  | .mk0 | .mk1 | .mk2 | .mk3 | .mk4 => ``Code.mk
  | .den0 | .den1 | .den2 | .den3 | .den4 => ``Code.den'

end AppState

def reportStagingError (name : MessageData) : CheckM α :=
  throwError m!"staging error: variable `{name}` is not available in the current staging context"

mutual

partial def checkStage (e : Expr) : CheckM Unit := do
  let { stagedFVarId? } ← read
  match e with
  | .app .. =>
      let state ← checkApp e
      if state.isUnsaturatedOp then
        throwError "invalid {state.opName} application"
  | .lam name domain body _ | .forallE name domain body _ =>
      checkStage domain
      pushBinder name
      checkStage body
      popBinder
  | .letE name type value body _ =>
      checkStage type
      checkStage value
      pushBinder name
      checkStage body
      popBinder
  | .bvar deBruijnIndex =>
      let binderStage ← binderStage deBruijnIndex
      let stage ← currentStage
      unless binderStage = stage do
        let name ← binderName deBruijnIndex
        reportStagingError m!"{name}"
  | .fvar fvarId =>
    unless stagedFVarId? == some fvarId do
      let fvarStage ← getFVarStage fvarId
      let stage ← currentStage
      unless stage = fvarStage do
        reportStagingError m!"{mkFVar fvarId}"
  | .mvar mvarId =>
      let some value ← getExprMVarAssignment? mvarId
        | throwError m!"staged term contains unresolved metavariable {mkMVar mvarId}"
      mvarId.withContext <| checkStage value
  | .mdata _ body | .proj _ _ body =>
      checkStage body
  | .sort .. | .const .. | .lit .. =>
      return

/-- Check the body of a denotational function without checking its
implementation-detail equality domain. -/
partial def checkDen (e : Expr) : CheckM Unit := do
  match e.consumeMData with
  | .lam name domain body _ =>
      let_expr Eq type interp den := domain
        | throwError "malformed denotational function"
      unless type.isConstOf ``Interp && den.isConstOf ``Interp.den do
        throwError "malformed denotational function"
      let_expr Staged.interp instStaged := interp
        | throwError "malformed denotational function"
      withReader ({ · with stagedFVarId? := instStaged.fvarId? }) do
        pushBinder name
        checkStage body
        popBinder
  | e =>
      checkStage e

partial def checkApp (e : Expr) : CheckM AppState := do
  let stage ← currentStage
  match e with
  | .app fn arg =>
      let state ← checkApp fn
      match state with
      | .regular | .den4 =>
          checkStage arg
      | .code1 | .mk1 | .mk2 =>
          pushSegment (stage + 1)
          checkDen arg
          popSegment
      | .den1 =>
          checkDen arg
      | .den2 =>
          pushSegment (stage - 1)
          checkStage arg
          popSegment
      | .code0 | .mk0 | .mk3 | .den0 | .den3 =>
          pure ()
      | .code2 | .mk4 =>
          unreachable!
      return state.next
  | fn =>
      let fn := fn.cleanupAnnotations
      let name := fn.constName
      if name == ``Code then
        return .code0
      else if name == ``Code.mk then
        return .mk0
      else if name == ``Code.den' then
        return .den0
      else
        checkStage fn
        return .regular

end

public def checkStages (e : Expr) (stagedFVarId? : Option FVarId := none)
    (startStage : Int := 0) : MetaM Unit :=
  (checkStage e)
    |>.run { stagedFVarId? }
    |>.run' {
      binders := #[]
      segmentStarts := #[0]
      segmentStages := #[startStage]
      segmentSizes := rfl
    }

end Thyme.Elab
