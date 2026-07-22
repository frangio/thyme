module

public meta import TMeta.Code
public meta import TMeta.Elab.Check
public meta import TMeta.Elab.TypedTransform
public meta import TMeta.Elab.Runtime
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.CollectFVars

namespace TMeta.Elab

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

open Lean Elab Term Meta

def mkArrayLitOf (type : Expr) (xs : Array α) (f : α → Expr) : MetaM Expr := do
  let u ← getDecLevel type
  let nil := mkApp (mkConst ``List.nil [u]) type
  let cons := mkApp (mkConst ``List.cons [u]) type
  let list := xs.foldr (fun x list => mkApp2 cons (f x) list) nil
  return mkApp2 (mkConst ``List.toArray [u]) type list

structure SpliceCapture where
  level : Level
  bodyType : Expr
  body : Expr

namespace SpliceCapture

def gen : SpliceCapture → Expr
  | { level, bodyType, body } =>
    mkApp2 (mkConst ``Code.gen [level]) bodyType body

def value : SpliceCapture → Expr
  | { level, bodyType, body } =>
    mkApp2 (mkConst ``Code.value [level]) bodyType body

end SpliceCapture

structure QuoteBody where
  template : QuoteTemplate
  splices : Array SpliceCapture

structure QuoteState where
  splices : Array SpliceCapture
  spliceHoles : Array MVarId
  deriving Inhabited

structure StageFrame where
  quote? : Option QuoteState := none
  /--
  An fvar `hFalse : False` introduced as a local assumption while
  building an `ExfCodegen`. A quote encountered while the assumption is
  present must become `Code.forge` rather than preserving a potentially
  open value term with `Code.quote`.
  -/
  hFalse? : Option Expr := none
  deriving Inhabited

structure TransformState where
  frames : Zipper StageFrame
  stage : Int
  deriving Inhabited

abbrev TransformM := StateT TransformState TermElabM

instance : Inhabited (TransformM α) := ⟨throw default⟩

namespace QuoteBody

def gen (quote : QuoteBody) : TransformM Expr := do
  let declName := (← getDeclName?).getD .anonymous
  let index ← quote.template.register declName
  let splices ← mkArrayLitOf (mkConst ``Codegen) quote.splices (·.gen)
  return mkApp3 (mkConst ``instantiateQuoteTemplate)
    (toExpr declName) (toExpr index) splices

end QuoteBody

def getFrame : TransformM StageFrame :=
  return (← get).frames.current

def getStage : TransformM Int :=
  return (← get).stage

def modifyFrame (f : StageFrame → StageFrame) : TransformM Unit :=
  modify fun s =>
    { s with frames := { s.frames with current := f s.frames.current } }

def modifyGetFrame (f : StageFrame → α × StageFrame) : TransformM α :=
  modifyGet fun s =>
    let (result, current) := f s.frames.current
    (result, { s with frames := { s.frames with current } })

def modifyQuote (f : QuoteState → QuoteState) : TransformM Unit :=
  modifyFrame fun frame => { frame with quote? := some (f frame.quote?.get!) }

def withSuccFrame (k : TransformM α) : TransformM α := do
  modify fun s => { s with
    frames := s.frames.moveRight
    stage := s.stage + 1
  }
  let result ← k
  modify fun s => { s with
    frames := s.frames.moveLeft
    stage := s.stage - 1
  }
  return result

def withPredFrame (k : TransformM α) : TransformM α := do
  modify fun s => { s with
    frames := s.frames.moveLeft
    stage := s.stage - 1
  }
  let result ← k
  modify fun s => { s with
    frames := s.frames.moveRight
    stage := s.stage + 1
  }
  return result

def withHFalse (k : Expr → TransformM α) : TransformM α :=
  withLocalDeclD `_hFalse (mkConst ``False) fun hFalse => do
    let saved ← modifyGetFrame fun current =>
      (current.hFalse?, { current with hFalse? := some hFalse })
    let result ← k hFalse
    modifyFrame fun current => { current with hFalse? := saved }
    return result

def withQuote (k : TransformM α) : TransformM (α × QuoteState) := do
  let saved ← modifyGetFrame fun current =>
    (current.quote?, { current with
      quote? := some { splices := #[], spliceHoles := #[] }
    })
  let result ← k
  let some quote ← modifyGetFrame fun current =>
    (current.quote?, { current with quote? := saved })
    | unreachable!
  return (result, quote)

def getHFalse? : TransformM (Option Expr) :=
  return (← getFrame).hFalse?

def getQuote? : TransformM (Option QuoteState) :=
  return (← getFrame).quote?

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

namespace TransformM

mutual

partial def transform := TypedTransform.transform getConstAppTransform?
partial def transformAppArgs := TypedTransform.transformAppArgs getConstAppTransform?

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
    TransformM (mode.Result Expr) := do
  let .const _ [level] := fn | unreachable!
  unless args.size ≥ 1 do throwError "invalid Code application"
  let type := args[0]!
  let type ← withSuccFrame <|
    transform (.expect (.sort level) #[]) type
  transformAppArgs mode (.app fn type) args
    (.sort (mkLevelMax' .one level)) #[] 1

partial def transformQuote (mode : TypeMode) (quoteFn : Expr) (args : Array Expr) :
    TransformM (mode.Result Expr) := do
  let .const _ [level] := quoteFn | unreachable!
  unless args.size = 3 do throwError "invalid Code.quote application"
  let sourceBody := args[1]!
  let mkCodeType type :=
    mkApp (mkConst ``Code [level]) type
  if let some hFalse ← getHFalse? then
    let mkCodeForge type hFalse gen :=
      mkApp3 (mkConst ``Code.forge [level]) type hFalse gen
    match mode with
    | .expect codeTypeAbs typeEnv =>
      let (.app _ typeAbs, typeEnv) ←
        view (·.isAppOfArity ``Code 1) codeTypeAbs typeEnv
        | throwError "Code expected"
      let type := instantiate typeAbs typeEnv
      let body ←
        withSuccFrame <| transformBody (.expect typeAbs typeEnv) sourceBody
      let gen ← body.gen
      return mkCodeForge type hFalse gen
    | .synth =>
      let body ←
        withSuccFrame <| transformBody .synth sourceBody
      let gen ← body.val.gen
      let type := body.type
      let expr := mkCodeForge type hFalse gen
      return .mk expr (mkCodeType type)
  else if (← getQuote?).isSome then
    withHFalse fun hFalse => do
      let body ←
        withSuccFrame <| transformBody .synth sourceBody
      let quote := body.val
      let gen ← quote.gen
      quote.template.withInstantiate quote.splices (pure ·.value) do
        let value ← instantiateMVars quote.template.body
        let type ← instantiateMVars body.type
        let xfc ← mkLambdaFVars #[hFalse] gen
        let expr := mkApp3 quoteFn type value xfc
        return .mk expr (mkCodeType type)
  else
    let type := args[0]!
    let xfc ← withHFalse fun hFalse => do
      let body ←
        withSuccFrame <| transformBody (.expect type #[]) sourceBody
      let gen ← body.gen
      mkLambdaFVars #[hFalse] gen
    let expr := mkApp3 quoteFn type sourceBody xfc
    return .mk expr (mkCodeType type)
where
  transformBody (mode : TypeMode) (sourceBody : Expr) :
      TransformM (mode.Result QuoteBody) := do
    let (body, { splices, spliceHoles }) ←
      withQuote <| transform mode sourceBody
    let mctx ← getMCtx
    return body.map fun body => {
      template := { body, spliceHoles, mctx }
      splices
    }

partial def transformSplice (mode : TypeMode) (spliceFn : Expr) (args : Array Expr) :
    TransformM (mode.Result Expr) := do
  let .const _ [level] := spliceFn | unreachable!
  unless args.size ≥ 2 do throwError "invalid Code.value application"
  let sourceBody := args[1]!
  if args.size = 2 then
    transformCore mode level sourceBody
  else
    let core ← transformCore .synth level sourceBody
    transformAppArgs mode core.val args core.typeAbs core.typeEnv 2
where
  transformCore (mode : TypeMode) (level : Level) (sourceBody : Expr) :
      TransformM (mode.Result Expr) := do
    if (← getQuote?).isSome then
      let (body, bodyType) ← withPredFrame <| transformBody sourceBody
      let type := match mode with
        | .expect typeAbs typeEnv => instantiate typeAbs typeEnv
        | .synth => bodyType
      let hole ← mkFreshExprMVar (some type) .syntheticOpaque
      modifyQuote fun quote => { quote with
        splices := quote.splices.push { level, bodyType, body }
        spliceHoles := quote.spliceHoles.push hole.mvarId!
      }
      return .mk hole bodyType
    else if (← getStage) ≤ 0 then
      withPredFrame <| withHFalse fun hFalse => do
        let (body, bodyType) ← transformBody sourceBody
        let gen := mkApp2 (mkConst ``Code.gen [level]) bodyType body
        let xfc ← mkLambdaFVars #[hFalse] gen
        let gen := mkApp (mkConst ``ExfCodegen.run) xfc
        let expr ← withFVarAxioms gen (liftM ∘ evalCodegen)
        return .mk expr bodyType
    else
      let (body, bodyType) ← withPredFrame <| transformBody sourceBody
      let expr := mkApp2 (mkConst ``Code.value [level]) bodyType body
      return .mk expr bodyType

  transformBody (sourceBody : Expr) : TransformM (Expr × Expr) := do
    let body ← transform .synth sourceBody
    let (.app _ typeAbs, typeEnv) ←
      view (·.isAppOfArity ``Code 1) body.typeAbs body.typeEnv
      | throwError "Code expected"
    let type := instantiate typeAbs typeEnv
    return (body.val, type)

end

end TransformM

def transform (expectedType : Expr) (e : Expr) : TermElabM Expr := do
  checkStages e
  let lctx ← instantiateLCtxMVars (← getLCtx)
  let localInstances ← getLocalInstances
  withLCtx lctx localInstances <| withMCtx {} <|
    (TransformM.transform (.expect expectedType #[]) e).run' {
      frames := { left := #[], current := {}, right := #[] }
      stage := 0
    }

end

end TMeta.Elab
