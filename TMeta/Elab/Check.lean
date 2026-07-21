module

public meta import TMeta.Code

open Lean Meta

namespace TMeta

meta section

structure CheckState where
  binders : Array Name
  segmentEnds : Array Nat
  segmentDepths : Array Int

abbrev CheckM := StateT CheckState MetaM

def pushBinder (name : Name) : CheckM PUnit :=
  modify fun ⟨binders, segmentEnds, segmentDepths⟩ =>
    ⟨binders.push name, segmentEnds, segmentDepths⟩

def popBinder : CheckM PUnit :=
  modify fun ⟨binders, segmentEnds, segmentDepths⟩ =>
    ⟨binders.pop, segmentEnds, segmentDepths⟩

def pushSegment (depth : Int) : CheckM PUnit :=
  modify fun ⟨binders, segmentEnds, segmentDepths⟩ =>
    ⟨binders, segmentEnds.push binders.size, segmentDepths.push depth⟩

def popSegment : CheckM PUnit :=
  modify fun ⟨binders, segmentEnds, segmentDepths⟩ =>
    ⟨binders, segmentEnds.pop, segmentDepths.pop⟩

def binderIndex (deBruijnIndex : Nat) : CheckM Nat := do
  let numBinders := (← get).binders.size
  unless deBruijnIndex < numBinders do
    throwError "unexpected loose bound variable #{deBruijnIndex}"
  return numBinders - (deBruijnIndex + 1)

def binderName (deBruijnIndex : Nat) : CheckM Name := do
  let index ← binderIndex deBruijnIndex
  return (← get).binders[index]!

def binderDepth (deBruijnIndex : Nat) : CheckM (Option Int) := do
  let index ← binderIndex deBruijnIndex
  let state ← get
  for h : offset in *...state.segmentEnds.size do
    let i := state.segmentEnds.size - (offset + 1)
    if state.segmentEnds[i] ≤ index then
      return state.segmentDepths[i + 1]?
  return state.segmentDepths[0]?

inductive AppState
  | regular
  | code0
  | code1
  | quote0
  | quote1
  | quote2
  | quote3
  | splice0
  | splice1
  | splice2
  deriving Inhabited

namespace AppState

def isUnsaturatedOp : AppState → Bool
  | .regular | .code1 | .quote3 | .splice2 => false
  | _ => true

def next : AppState → AppState
  | .regular => .regular
  | .code0 => .code1
  | .code1 => unreachable!
  | .quote0 => .quote1
  | .quote1 => .quote2
  | .quote2 => .quote3
  | .quote3 => unreachable!
  | .splice0 => .splice1
  | .splice1 => .splice2
  | .splice2 => .regular

def opName : AppState → Name
  | .regular => unreachable!
  | .code0 | .code1 => ``Code
  | .quote0 | .quote1 | .quote2 | .quote3 => ``Code.quote
  | .splice0 | .splice1 | .splice2 => ``Code.value

end AppState

mutual

partial def checkStage (e : Expr) (depth : Int) : CheckM Unit := do
  match e with
  | .app .. =>
      let state ← checkApp e depth
      if state.isUnsaturatedOp then
        throwError "invalid {state.opName} application"
  | .lam name domain body _ | .forallE name domain body _ =>
      checkStage domain depth
      pushBinder name
      checkStage body depth
      popBinder
  | .letE name type value body _ =>
      checkStage type depth
      checkStage value depth
      pushBinder name
      checkStage body depth
      popBinder
  | .bvar deBruijnIndex =>
      let some binderDepth ← binderDepth deBruijnIndex | return
      unless binderDepth = depth do
        let name ← binderName deBruijnIndex
        throwError m!"stage mismatch: bound variable `{name}` is available at stage \
          {binderDepth}, but is used at stage {depth}"
  | .fvar fvarId =>
      unless depth = 0 do
        throwError m!"stage mismatch: local {mkFVar fvarId} is available at stage 0, \
          but is used at stage {depth}"
  | .mvar mvarId =>
      throwError m!"staged term contains unresolved metavariable {mkMVar mvarId}"
  | .mdata _ body | .proj _ _ body =>
      checkStage body depth
  | .sort .. | .const .. | .lit .. =>
      return

partial def checkApp (e : Expr) (depth : Int) : CheckM AppState := do
  match e with
  | .app fn arg =>
      let state ← checkApp fn depth
      match state with
      | .regular | .splice0 | .splice2 =>
          checkStage arg depth
      | .code0 | .quote0 | .quote1 =>
          pushSegment depth
          checkStage arg (depth + 1)
          popSegment
      | .splice1 =>
          pushSegment depth
          checkStage arg (depth - 1)
          popSegment
      | .quote2 =>
          pure ()
      | .code1 | .quote3 =>
          throwError "invalid {state.opName} application"
      return state.next
  | fn =>
      let fn := fn.cleanupAnnotations
      let name := fn.constName
      if name == ``Code then
        return .code0
      else if name == ``Code.quote then
        return .quote0
      else if name == ``Code.value then
        return .splice0
      else
        checkStage fn depth
        return .regular

end

public def checkStages (e : Expr) : MetaM Unit :=
  (checkStage e 0).run' { binders := #[], segmentEnds := #[], segmentDepths := #[] }

end

end TMeta
