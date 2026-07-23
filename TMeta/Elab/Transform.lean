module

public meta import TMeta.Code
public meta import TMeta.Elab.Check
public meta import TMeta.Elab.OpTransform
public meta import TMeta.Elab.Runtime
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Check
public meta import Lean.Meta.Eval

namespace TMeta.Elab

meta section

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

unsafe def evalCodegenImpl (gen : Expr) : MetaM Expr := do
  let result ← evalExpr Codegen (mkConst ``Codegen) gen
  result.run

@[implemented_by evalCodegenImpl]
opaque evalCodegen (gen : Expr) : MetaM Expr

public meta register_option tmeta.checkCoherence : Bool := {
  defValue := false
  descr := "check that generated code is definitionally equal to its denotation"
}

def mkArrayLitOf (type : Expr) (xs : Array α) (f : α → Expr) : MetaM Expr := do
  let u ← getDecLevel type
  let nil := .app (mkConst ``List.nil [u]) type
  let cons := .app (mkConst ``List.cons [u]) type
  let list := xs.foldr (fun x list => mkApp2 cons (f x) list) nil
  return mkApp2 (mkConst ``List.toArray [u]) type list

structure SpliceCapture where
  level : Level
  type : Expr
  body : Expr
  gen : Expr

structure QuoteState where
  lctxStart : Nat
  splices : Array SpliceCapture
  spliceHoles : Array MVarId
  deriving Inhabited

structure TransformState where
  frames : Zipper (Option QuoteState)
  stage : Int
  deriving Inhabited

abbrev TransformM := StateT TransformState TermElabM

instance : Inhabited (TransformM α) := ⟨throw default⟩

def getStage : TransformM Int :=
  return (← get).stage

def getQuote? : TransformM (Option QuoteState) :=
  return (← get).frames.current

def modifyQuote (f : QuoteState → QuoteState) : TransformM Unit :=
  modify fun s => { s with
    frames := { s.frames with current := some (f s.frames.current.get!) }
  }

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

def withQuote (k : TransformM α) : TransformM (α × QuoteState) := do
  let lctxStart := (← getLCtx).numIndices
  let saved ← modifyGet fun s =>
    (s.frames.current, { s with frames := { s.frames with
      current := some { lctxStart, splices := #[], spliceHoles := #[] }
    } })
  let result ← k
  let some quote ← modifyGet fun s =>
    (s.frames.current, { s with frames := { s.frames with current := saved } })
    | unreachable!
  return (result, quote)

/--
Closes a `Codegen` expression over the live local declarations from
`start` onward. Each declaration becomes a thunk parameter, with
occurrences in later declaration types and `e` replaced by calls to the
corresponding thunk. The parameters are discharged with `Codegen.abs` and
must never be forced by the resulting generator.
-/
def closeLCtxRange (start : Nat) (e : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let decls := Array.emptyWithCapacity (lctx.numIndices - start) |>
    lctx.foldl .push (start := start)
  let fvars := decls.map fun decl => Expr.fvar decl.fvarId
  let unit := Lean.mkConst ``Unit.unit
  let thunks :=
    Array.ofFn (n := decls.size) fun i => .app (.bvar (decls.size - 1 - i)) unit
  let types := decls.mapIdx fun i decl =>
    decl.type.abstractRange i fvars
      |>.instantiateRevRange (decls.size - i) decls.size thunks
  have : types.size = decls.size := by simp [types]
  let body := (e.abstract fvars).instantiateRev thunks
  decls.size.foldRevM (init := body) fun i h body => do
    let decl := decls[i]
    let type := types[i]
    let level ← getLevel decl.type
    let thunkType := mkSimpleThunkType (type.liftLooseBVars 0 1)
    let k := .lam decl.userName thunkType body .default
    return mkApp2 (mkConst ``Codegen.abs [level]) type k

namespace TransformM

mutual

partial def transform := OpTransform.transform getOpAppTransform

partial def getOpAppTransform : Name → OpTransform.OpAppTransform TransformM
  | name =>
    if name == ``Code then
      .transform transformCode
    else if name == ``Code.quote then
      .transform transformQuote
    else if name == ``Code.val then
      .transform transformSplice
    else if name == ``Code.mk! then
      -- `Code.mk!` was produced by an earlier staging transformation, so its
      -- arguments have already been checked and transformed.
      .skip 3
    else
      .default

partial def transformCode (fn : Expr) (args : Vector Expr 1) : TransformM Expr := do
  let .const _ [level] := fn | unreachable!
  let type ← withSuccFrame <| transform args[0]
  return .app fn type

partial def transformQuote (quoteFn : Expr) (args : Vector Expr 2) : TransformM Expr := do
  let .const _ [level] := quoteFn | unreachable!
  let type := args[0]
  let sourceBody := args[1]
  let (body, { splices, spliceHoles, .. }) ←
    withSuccFrame <| withQuote <| transform sourceBody
  let template := { body, spliceHoles, mctx := ← getMCtx : QuoteTemplate }
  let declName := (← getDeclName?).getD .anonymous
  let index ← template.register declName
  let spliceGens ← splices.mapM fun splice => instantiateMVars splice.gen
  let spliceGens ← mkArrayLitOf (mkConst ``Codegen) spliceGens id
  let action := mkApp3 (mkConst ``instantiateQuoteTemplate)
    (toExpr declName) (toExpr index) spliceGens
  let gen := .app (mkConst ``Codegen.mk) action
  let value ← template.instantiate splices fun s =>
    pure <| mkApp2 (mkConst ``Code.val [s.level]) s.type s.body
  let get := mkSimpleThunk value
  return mkApp3 (mkConst ``Code.mk! [level]) type get gen

partial def transformSplice (spliceFn : Expr) (args : Vector Expr 2) : TransformM Expr := do
  let .const _ [level] := spliceFn | unreachable!
  let type := args[0]
  let sourceBody := args[1]
  let body ← withPredFrame <| transform sourceBody
  if let some quote ← getQuote? then
    let gen := mkApp2 (mkConst ``Code.gen [level]) type body
    let gen ← closeLCtxRange quote.lctxStart gen
    let hole ← mkFreshExprMVar (some type) .syntheticOpaque
    modifyQuote fun quote => { quote with
      splices := quote.splices.push { level, type, body, gen }
      spliceHoles := quote.spliceHoles.push hole.mvarId!
    }
    return hole
  else if (← getStage) ≤ 0 then
    let gen := mkApp2 (mkConst ``Code.gen [level]) type body
    let gen ← closeLCtxRange 0 gen
    let result ← evalCodegen gen
    if ← tmeta.checkCoherence.getM then
      let denotation := mkApp2 spliceFn type sourceBody
      unless ← withNewMCtxDepth <| isDefEqGuarded result denotation do
        let note ← withNewMCtxDepth <| mkUnfoldAxiomsNote result denotation
        throwError m!"generated code is not definitionally equal to its denotation\n\
          generated:{indentExpr result}\n\
          denotation:{indentExpr denotation}{note}"
    return result
  else
    return mkApp2 (mkConst ``Code.val [level]) type body

end

end TransformM

public def transform (e : Expr) : TermElabM Expr := do
  checkStages e
  let lctx ← instantiateLCtxMVars (← getLCtx)
  let localInstances ← getLocalInstances
  withLCtx lctx localInstances <| withMCtx {} <|
    (TransformM.transform e).run' {
      frames := { left := #[], current := none, right := #[] }
      stage := 0
    }

end

end TMeta.Elab
