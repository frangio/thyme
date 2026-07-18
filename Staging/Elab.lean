module

public import Staging.Elab.Runtime
public meta import Staging.Code
public meta import Staging.Check
public meta import Staging.TypedTransform
public meta import Staging.Elab.Runtime
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.CollectFVars
public meta import Lean.PrettyPrinter.Delaborator

namespace Staging

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

open Lean Elab Term Meta Staging

structure QuoteState where
  spliceGens : Array Expr
  spliceHoles : Array MVarId
  deriving Inhabited

structure StageFrame where
  quote? : Option QuoteState := none
  deriving Inhabited

structure StagingState where
  frames : Zipper StageFrame
  depth : Int
  deriving Inhabited

def StagingState.initial : StagingState where
  frames := {
    left := #[]
    current := {}
    right := #[]
  }
  depth := 0

structure StagingContext where
  hFalse? : Option Expr

abbrev StagingM := ReaderT StagingContext (StateT StagingState TermElabM)

instance : Inhabited (StagingM α) := ⟨throw default⟩
instance : Nonempty (StagingM α) := ⟨throw default⟩

def getFrame : StagingM StageFrame :=
  return (← getThe StagingState).frames.current

def getDepth : StagingM Int :=
  return (← getThe StagingState).depth

def modifyFrame (f : StageFrame → StageFrame) : StagingM Unit :=
  modifyThe StagingState fun s =>
    { s with frames := { s.frames with current := f s.frames.current } }

def modifyGetFrame (f : StageFrame → α × StageFrame) : StagingM α :=
  modifyGetThe StagingState fun s =>
    let (result, current) := f s.frames.current
    (result, { s with frames := { s.frames with current } })

def withSuccFrame (k : StagingM α) : StagingM α := do
  modifyThe StagingState fun s => { s with
    frames := s.frames.moveRight
    depth := s.depth + 1
  }
  let result ← k
  modifyThe StagingState fun s => { s with
    frames := s.frames.moveLeft
    depth := s.depth - 1
  }
  return result

def withPredFrame (k : StagingM α) : StagingM α := do
  modifyThe StagingState fun s => { s with
    frames := s.frames.moveLeft
    depth := s.depth - 1
  }
  let result ← k
  modifyThe StagingState fun s => { s with
    frames := s.frames.moveRight
    depth := s.depth + 1
  }
  return result

def withHFalse (k : Expr → StagingM α) : StagingM α :=
  withLocalDeclD `_hFalse (mkConst ``False) fun hFalse =>
    withReader
      (fun ctx => { ctx with hFalse? := some hFalse })
      (k hFalse)

def withQuote (k : StagingM α) : StagingM α := do
  let saved ← modifyGetFrame fun current =>
    (current.quote?, { current with
      quote? := some { spliceGens := #[], spliceHoles := #[] }
    })
  let result ← k
  modifyFrame fun current => { current with quote? := saved }
  return result

def getHFalse? : StagingM (Option Expr) :=
  return (← readThe StagingContext).hFalse?

def withFVarAxioms (e : Expr) (k : Expr → StagingM α) : StagingM α :=
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

partial def getConstAppTransform? (name : Name) : Option (ConstAppTransform StagingM) :=
  if name == ``Code then
    some transformCode
  else if name == ``Code.quote then
    some transformQuote
  else if name == ``Code.splice then
    some transformSplice
  else
    none

partial def transformCode (mode : TypeMode) (fn : Expr) (args : Array Expr) :
    StagingM mode.Result := do
  let .const ``Code [level] := fn | unreachable!
  unless args.size ≥ 1 do throwError "invalid Code application"
  let type := args[0]!
  let type ← withSuccFrame (transform (.expect (.sort level) #[]) type)
  transformAppArgs mode (.app fn type) args
    (.sort (mkLevelMax' .one level)) #[] 1

partial def transformQuote (mode : TypeMode) (quoteFn : Expr) (args : Array Expr) :
    StagingM mode.Result := do
  let .const ``Code.quote [level] := quoteFn | unreachable!
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
    StagingM mode.Result := do
  let .const ``Code.splice [level] := spliceFn | unreachable!
  unless args.size ≥ 2 do throwError "invalid Code.splice application"
  let sourceBody := args[1]!
  if args.size = 2 then
    transformCore mode level sourceBody
  else
    let core ← transformCore .synth level sourceBody
    transformAppArgs mode core.expr args core.typeAbs core.typeEnv 2
where
  transformCore (mode : TypeMode) (level : Level) (sourceBody : Expr) :
      StagingM mode.Result := do
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
      let expr := mkApp2 (mkConst ``Code.splice [level]) bodyType body
      return mode.mkResult expr type

  transformBody (sourceBody : Expr) : StagingM (Expr × Expr) := do
    let body ← withPredFrame (transform .synth sourceBody)
    let (.app _ typeAbs, typeEnv) ←
      view (·.isAppOfArity ``Code 1) body.typeAbs body.typeEnv
      | throwError "Code expected"
    let type := instantiate typeAbs typeEnv
    return (body.expr, type)

end

public meta register_option staging.raw : Bool := {
  defValue := false
  descr := "elaborate staging syntax without compiling it"
}

public meta def withCodeReducible (k : TermElabM α) : TermElabM α := do
  let quoteStatus ← getReducibilityStatus ``Code.quote
  let spliceStatus ← getReducibilityStatus ``Code.splice
  try
    setReducibilityStatus ``Code.quote .reducible
    setReducibilityStatus ``Code.splice .reducible
    k
  finally
    setReducibilityStatus ``Code.quote quoteStatus
    setReducibilityStatus ``Code.splice spliceStatus

public meta def elabStagingTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  if staging.raw.get (← getOptions) then
    elabTermEnsuringType stx expectedType?
  else
    let raw ← withCodeReducible do
      let raw ← withOptions (staging.raw.set · true) do
        elabTermEnsuringType stx expectedType?
      synthesizeSyntheticMVars
      instantiateMVars raw
    if raw.hasMVar then
      tryPostpone
      throwError "staging expression contains unresolved metavariables"
    checkStages raw
    let expectedType ← match expectedType? with
      | some expectedType => instantiateMVars expectedType
      | none => inferType raw
    let lctx ← instantiateLCtxMVars (← getLCtx)
    let localInstances ← getLocalInstances
    let ctx : StagingContext := {
      hFalse? := none
    }
    let state := StagingState.initial
    let (result, _) ← withLCtx lctx localInstances <| withMCtx {} <| StateT.run
      ((transform (.expect expectedType #[]) raw) ctx) state
    ensureHasType expectedType? result

public section

syntax:max (name := codeStx) "Code " term:arg : term
syntax:max (name := bareCodeStx) "Code" : term
syntax:max (name := quoteStx) "`⟨" term "⟩" : term
syntax:max (name := spliceStx) "~" term:max : term

open PrettyPrinter Delaborator
open PrettyPrinter.Delaborator.SubExpr

@[app_delab Staging.Code]
meta def delabCode : Delab := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  match (← getExpr).getAppNumArgs with
  | 0 =>
    `(Code)
  | 1 =>
    let type ← withNaryArg 0 delab
    `(Code $type)
  | _ =>
    failure

@[app_delab Code.quote]
meta def delabQuote : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
  let value ← withNaryArg 1 delab
  `(`⟨$value⟩)

@[app_delab Code.splice]
meta def delabSplice : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 2 do
  let body ← withNaryArg 1 delab
  `(~$body)

@[term_elab codeStx]
meta def elabCode : TermElab := fun stx expectedType? => do
  let `(Code $type) := stx | throwUnsupportedSyntax
  elabStagingTerm (← ``(Staging.Code $type)) expectedType?

@[term_elab bareCodeStx]
meta def elabBareCode : TermElab := fun stx expectedType? => do
  elabTerm (mkIdentFrom stx ``Staging.Code) expectedType?

@[term_elab quoteStx]
meta def elabQuote : TermElab := fun stx expectedType? => do
  let `(`⟨$value⟩) := stx | throwUnsupportedSyntax
  elabStagingTerm (← ``(Staging.Code.quote $value)) expectedType?

@[term_elab spliceStx]
meta def elabSplice : TermElab := fun stx expectedType? => do
  let `(~$body) := stx | throwUnsupportedSyntax
  elabStagingTerm (← ``(Staging.Code.splice $body)) expectedType?

end

end

end Staging
