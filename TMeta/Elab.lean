module

public import TMeta.Elab.Runtime
public meta import TMeta.Code
public meta import TMeta.Check
public meta import TMeta.TypedTransform
public meta import TMeta.Elab.Runtime
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.CollectFVars
public meta import Lean.PrettyPrinter.Delaborator

namespace TMeta

public meta section

structure Zipper (α : Type u) where
  left : Array α
  current : α
  right : Array α
  deriving Inhabited

namespace Zipper

def moveRight [Inhabited α] (z : Zipper α) : Zipper α where
  left := z.left.push z.current
  current := z.right.back?.getD default
  right := z.right.pop

def moveLeft [Inhabited α] (z : Zipper α) : Zipper α where
  left := z.left.pop
  current := z.left.back?.getD default
  right := z.right.push z.current

end Zipper

open Lean Elab Term Meta TMeta

structure QuoteState where
  spliceGens : Array Expr
  spliceHoles : Array MVarId
  deriving Inhabited

structure StageFrame where
  quote? : Option QuoteState := none
  deriving Inhabited

structure TransformState where
  frames : Zipper StageFrame
  depth : Int
  deriving Inhabited

def TransformState.initial : TransformState where
  frames := {
    left := #[]
    current := {}
    right := #[]
  }
  depth := 0

structure TransformContext where
  hFalse? : Option Expr

abbrev TransformM := ReaderT TransformContext (StateT TransformState TermElabM)

instance : Inhabited (TransformM α) := ⟨throw default⟩
instance : Nonempty (TransformM α) := ⟨throw default⟩

def getFrame : TransformM StageFrame :=
  return (← getThe TransformState).frames.current

def getDepth : TransformM Int :=
  return (← getThe TransformState).depth

def modifyFrame (f : StageFrame → StageFrame) : TransformM Unit :=
  modifyThe TransformState fun s =>
    { s with frames := { s.frames with current := f s.frames.current } }

def modifyGetFrame (f : StageFrame → α × StageFrame) : TransformM α :=
  modifyGetThe TransformState fun s =>
    let (result, current) := f s.frames.current
    (result, { s with frames := { s.frames with current } })

def withSuccFrame (k : TransformM α) : TransformM α := do
  modifyThe TransformState fun s => { s with
    frames := s.frames.moveRight
    depth := s.depth + 1
  }
  let result ← k
  modifyThe TransformState fun s => { s with
    frames := s.frames.moveLeft
    depth := s.depth - 1
  }
  return result

def withPredFrame (k : TransformM α) : TransformM α := do
  modifyThe TransformState fun s => { s with
    frames := s.frames.moveLeft
    depth := s.depth - 1
  }
  let result ← k
  modifyThe TransformState fun s => { s with
    frames := s.frames.moveRight
    depth := s.depth + 1
  }
  return result

def withHFalse (k : Expr → TransformM α) : TransformM α :=
  withLocalDeclD `_hFalse (mkConst ``False) fun hFalse =>
    withReader
      (fun ctx => { ctx with hFalse? := some hFalse })
      (k hFalse)

def withQuote (k : TransformM α) : TransformM α := do
  let saved ← modifyGetFrame fun current =>
    (current.quote?, { current with
      quote? := some { spliceGens := #[], spliceHoles := #[] }
    })
  let result ← k
  modifyFrame fun current => { current with quote? := saved }
  return result

def getHFalse? : TransformM (Option Expr) :=
  return (← readThe TransformContext).hFalse?

def withFVarAxioms (e : Expr) (k : Expr → TransformM α) : TransformM α :=
  withoutModifyingEnv do
    let (_, used) ← e.collectFVars.run {}
    let used ← used.addDependencies
    let fvars := (← sortFVarIds used.fvarIds).map .fvar
    let mut axioms := .emptyWithCapacity fvars.size
    for fvar in fvars do
      let decl ← fvar.fvarId!.getDecl
      let type := (decl.type.abstractRange axioms.size fvars).instantiateRev axioms
      let name ← mkAuxDeclName decl.userName
      let levelParams := (collectLevelParams {} type).params.toList
      addDecl <| .axiomDecl { name, levelParams, type, isUnsafe := false }
      axioms := axioms.push (mkConst name (levelParams.map .param))
    k (e.replaceFVars fvars axioms)

mutual

partial def transform := Transform.transform getConstAppTransform?
partial def transformAppArgs := Transform.transformAppArgs getConstAppTransform?

partial def getConstAppTransform? (name : Name) : Option (ConstAppTransform TransformM) :=
  if name == ``Code then
    some transformCode
  else if name == ``Code.quote then
    some transformQuote
  else if name == ``Code.value then
    some transformSplice
  else
    none

partial def transformCode (mode : TypeMode) (fn : Expr) (args : Array Expr) :
    TransformM mode.Result := do
  let .const _ [level] := fn | unreachable!
  unless args.size ≥ 1 do throwError "invalid Code application"
  let type := args[0]!
  let type ← withSuccFrame (transform (.expect (.sort level) #[]) type)
  transformAppArgs mode (.app fn type) args
    (.sort (mkLevelMax' .one level)) #[] 1

partial def transformQuote (mode : TypeMode) (quoteFn : Expr) (args : Array Expr) :
    TransformM mode.Result := do
  let .const _ [level] := quoteFn | unreachable!
  unless args.size = 3 do throwError "invalid Code.quote application"
  let sourceBody := args[1]!
  let mkCodeType type :=
    mkApp (mkConst ``Code [level]) type
  let mkForgedCode type hFalse gen :=
    mkApp3 (mkConst ``Code.forge [level]) type hFalse gen
  if let some hFalse ← getHFalse? then
    match mode with
    | .expect codeTypeAbs typeEnv =>
      let (.app _ typeAbs, typeEnv) ←
        view (·.isAppOfArity ``Code 1) codeTypeAbs typeEnv
        | throwError "Code expected"
      let (gen, typeAbs, typeEnv) ←
        transformBody (.expect typeAbs typeEnv) sourceBody
      let type := instantiate typeAbs typeEnv
      return mkForgedCode type hFalse gen
    | .synth =>
      let (gen, typeAbs, typeEnv) ← transformBody .synth sourceBody
      let type := instantiate typeAbs typeEnv
      let expr := mkForgedCode type hFalse gen
      return { expr, typeAbs := mkCodeType type, typeEnv := #[] }
  else
    let type := args[0]!
    let xfc ← withHFalse fun hFalse => do
      let (gen, _, _) ← transformBody (.expect type #[]) sourceBody
      mkLambdaFVars #[hFalse] gen
    let expr := mkApp3 quoteFn type sourceBody xfc
    return mode.mkResult expr (mkCodeType type)
where
  transformBody (mode : TypeMode) (sourceBody : Expr) :=
    withSuccFrame <| withQuote do
      let body ← transform mode sourceBody
      let (body, typeAbs, typeEnv) :=
        match mode, body with
        | .synth, { expr, typeAbs, typeEnv } => (expr, typeAbs, typeEnv)
        | .expect typeAbs typeEnv, expr => (expr, typeAbs, typeEnv)
      let some { spliceGens, spliceHoles } := (← getFrame).quote? | unreachable!
      let template := { body, spliceHoles, mctx := ← getMCtx }
      let declName := (← getDeclName?).getD .anonymous
      let index ← registerQuoteTemplate declName template
      let spliceGensExpr ← mkArrayLit (mkConst ``Codegen) spliceGens.toList
      let gen := mkApp3 (mkConst ``instantiateQuoteTemplate)
        (toExpr declName) (toExpr index) spliceGensExpr
      return (gen, typeAbs, typeEnv)

partial def transformSplice (mode : TypeMode) (spliceFn : Expr) (args : Array Expr) :
    TransformM mode.Result := do
  let .const _ [level] := spliceFn | unreachable!
  unless args.size ≥ 2 do throwError "invalid Code.value application"
  let sourceBody := args[1]!
  if args.size = 2 then
    transformCore mode level sourceBody
  else
    let core ← transformCore .synth level sourceBody
    transformAppArgs mode core.expr args core.typeAbs core.typeEnv 2
where
  transformCore (mode : TypeMode) (level : Level) (sourceBody : Expr) :
      TransformM mode.Result := do
    if (← getFrame).quote?.isSome then
      let (body, bodyType) ← transformBody sourceBody
      let type : Expr := match mode with
        | .expect typeAbs typeEnv => instantiate typeAbs typeEnv
        | .synth => bodyType
      let gen := mkApp2 (mkConst ``Code.gen [level]) bodyType body
      let hole ← mkFreshExprMVar type .syntheticOpaque
      modifyFrame fun frame => { frame with
        quote? :=
          let quote := frame.quote?.get!
          some { quote with
            spliceGens := quote.spliceGens.push gen
            spliceHoles := quote.spliceHoles.push hole.mvarId!
          }
      }
      return mode.mkResult hole type
    else if (← getDepth) ≤ 0 then
      withHFalse fun hFalse => do
        let (body, bodyType) ← transformBody sourceBody
        let type : Expr := match mode with
          | .expect typeAbs typeEnv => instantiate typeAbs typeEnv
          | .synth => bodyType
        let gen := mkApp2 (mkConst ``Code.gen [level]) bodyType body
        let xfc ← mkLambdaFVars #[hFalse] gen
        let gen := mkApp (mkConst ``ExfCodegen.run) xfc
        let expr ← withFVarAxioms gen (liftM ∘ evalCodegen)
        return mode.mkResult expr type
    else
      let (body, bodyType) ← transformBody sourceBody
      let type : Expr := match mode with
        | .expect typeAbs typeEnv => instantiate typeAbs typeEnv
        | .synth => bodyType
      let expr := mkApp2 (mkConst ``Code.value [level]) bodyType body
      return mode.mkResult expr type

  transformBody (sourceBody : Expr) : TransformM (Expr × Expr) := do
    let body ← withPredFrame (transform .synth sourceBody)
    let (.app _ typeAbs, typeEnv) ←
      view (·.isAppOfArity ``Code 1) body.typeAbs body.typeEnv
      | throwError "Code expected"
    let type := instantiate typeAbs typeEnv
    return (body.expr, type)

end

public meta register_option tmeta.raw : Bool := {
  defValue := false
  descr := "elaborate TMeta syntax without compiling it"
}

public meta def withCodeReducible (k : TermElabM α) : TermElabM α := do
  let quoteStatus ← getReducibilityStatus ``Code.quote
  let valueStatus ← getReducibilityStatus ``Code.value
  try
    setReducibilityStatus ``Code.quote .reducible
    setReducibilityStatus ``Code.value .reducible
    k
  finally
    setReducibilityStatus ``Code.quote quoteStatus
    setReducibilityStatus ``Code.value valueStatus

def ensureNoMVars (e : Expr) : TermElabM Unit := do
  if e.hasMVar then
    tryPostpone
    let mvars ← getMVars e
    if ← logUnassignedUsingErrorInfos mvars then
      throwAbortTerm
    let levelMVars := (collectLevelMVars {} e).result
    if ← logUnassignedLevelMVarsUsingErrorInfos levelMVars then
      throwAbortTerm
    throwMVarError <| m!"staged term contains unresolved metavariables\n\
      {MessageData.joinSep (mvars.toList.map MessageData.ofGoal) m!"\n\n"}"

public meta def elabStagedTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  if tmeta.raw.get (← getOptions) then
    elabTermEnsuringType stx expectedType?
  else
    let raw ← withCodeReducible do
      let raw ← withOptions (tmeta.raw.set · true) do
        elabTermEnsuringType stx expectedType?
      synthesizeSyntheticMVarsNoPostponing
      instantiateMVars raw
    ensureNoMVars raw
    checkStages raw
    let expectedType ← match expectedType? with
      | some expectedType => instantiateMVars expectedType
      | none => inferType raw
    let lctx ← instantiateLCtxMVars (← getLCtx)
    let localInstances ← getLocalInstances
    let ctx : TransformContext := {
      hFalse? := none
    }
    let state := TransformState.initial
    let (result, _) ← withLCtx lctx localInstances <| withMCtx {} <| StateT.run
      ((transform (.expect expectedType #[]) raw) ctx) state
    ensureHasType expectedType? result

public section

syntax:max (name := codeStx) "Code " term:arg : term
syntax:max (name := bareCodeStx) "Code" : term
syntax:max (name := quoteStx) "`⟨" term "⟩" : term
syntax:max (name := spliceStx) "~" term:max : term

@[term_elab codeStx]
meta def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $type) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code $type)) expectedType?

@[term_elab bareCodeStx]
meta def elabBareCode : TermElab := fun stx expectedType? => do
  elabTerm (mkIdentFrom stx ``TMeta.Code) expectedType?

@[term_elab quoteStx]
meta def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$value⟩) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code.quote $value)) expectedType?

@[term_elab spliceStx]
meta def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$body) := stx | throwUnsupportedSyntax
  elabStagedTerm (← ``(TMeta.Code.value $body)) expectedType?

open PrettyPrinter Delaborator
open PrettyPrinter.Delaborator.SubExpr

private def ppSpliceNotation := `TMeta.pp.spliceNotation

private def withSpliceNotation (x : DelabM α) : DelabM α :=
  withOptions (·.setBool ppSpliceNotation true) x

@[app_delab TMeta.Code]
meta def delabCode : Delab := do
  match (← getExpr).getAppNumArgs with
  | 0 =>
    `(Code)
  | 1 =>
    let type ← withNaryArg 0 <| withSpliceNotation delab
    `(Code $type)
  | _ =>
    failure

@[app_delab Code.quote]
meta def delabQuote : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
  let value ← withNaryArg 1 <| withSpliceNotation delab
  `(`⟨$value⟩)

@[app_delab Code.value]
meta def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  guard <| (← getOptions).getBool ppSpliceNotation
  let body ← withNaryArg 1 delab
  `(~$body)

@[app_delab ExfCodegen.squash]
meta def delabExfCodegenSquash : Delab := withOverApp 1 do
  `(⋯)

@[app_delab ExfCodegen.default]
meta def delabExfCodegenDefault : Delab := `(⋯)

end

end

end TMeta
