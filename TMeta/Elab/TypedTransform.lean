module

public import Lean.Meta.InferType

open Lean Meta

namespace TMeta.Elab

public section

def instantiate (typeAbs : Expr) (typeEnv : Array Expr) : Expr :=
  typeAbs.instantiateBetaRevRange 0 typeEnv.size typeEnv

@[inline]
def view (p : Expr → Bool) (typeAbs : Expr) (typeEnv : Array Expr) :
    MetaM (Expr × Array Expr) := do
  if p typeAbs then
    return (typeAbs, typeEnv)
  else
    return (← whnf (instantiate typeAbs typeEnv), #[])

structure TypedResult (α : Type u) where
  val : α
  typeAbs : Expr
  typeEnv : Array Expr
  deriving Inhabited

inductive TypeMode where
  | expect (typeAbs : Expr) (typeEnv : Array Expr)
  | synth

abbrev TypeMode.Result (mode : TypeMode) (α : Type u) : Type u :=
  match mode with
  | .expect .. => α
  | .synth => TypedResult α

namespace TypeMode.Result

@[expose, macro_inline]
def mk (val : α) (typeAbs : Expr) (typeEnv : Array Expr := #[]) :
    {mode : TypeMode} → mode.Result α
  | .expect .. => val
  | .synth => { val, typeAbs, typeEnv }

def val : {mode : TypeMode} → mode.Result α → α
  | .expect .., result => result
  | .synth, result => TypedResult.val result

def typeAbs : {mode : TypeMode} → mode.Result α → Expr
  | .expect typeAbs _, _ => typeAbs
  | .synth, result => TypedResult.typeAbs result

def typeEnv : {mode : TypeMode} → mode.Result α → Array Expr
  | .expect _ typeEnv, _ => typeEnv
  | .synth, result => TypedResult.typeEnv result

def type {mode : TypeMode} (result : mode.Result α) : Expr :=
  instantiate result.typeAbs result.typeEnv

def sortLevel! {mode : TypeMode} (result : mode.Result α) : MetaM Level := do
  let (.sort level, _) ← view Expr.isSort result.typeAbs result.typeEnv
    | throwError "type expected"
  return level

def map (f : α → β) : {mode : TypeMode} → mode.Result α → mode.Result β
  | .expect .., result => f result
  | .synth, result => { result with val := f (TypedResult.val result) }

end TypeMode.Result

@[expose, macro_inline]
def TypeMode.mkResultM [Monad m] (val : α) (type : m Expr) :
    (mode : TypeMode) → m (mode.Result α)
  | .expect .. => return val
  | .synth => return { val, typeAbs := ← type, typeEnv := #[] }

abbrev ConstAppTransform (m : Type → Type) :=
  (mode : TypeMode) → (fn : Expr) → (args : Array Expr) → m (mode.Result Expr)

abbrev GetConstAppTransform? (m : Type → Type) :=
  Name → Option (ConstAppTransform m)

namespace TypedTransform

variable [Monad m] [MonadEnv m] [MonadError m]
  [MonadLiftT MetaM m] [MonadControlT MetaM m]

local instance [MonadExceptOf Exception m] : Nonempty (m α) :=
  ⟨throw default⟩

variable (onConstApp? : GetConstAppTransform? m)

mutual

partial def transform (mode : TypeMode) (e : Expr) : m (mode.Result Expr) := do
  match e with
  | .app .. =>
      transformApp mode e
  | .lam .. | .letE .. =>
      transformLambdaLet mode e #[]
  | .forallE .. =>
      transformForall mode e #[]
  | .mdata _ body =>
      let body ← transform mode body
      return body.map fun body => e.updateMData! body
  | .proj _ _ body =>
      let body ← transform .synth body
      let expr := e.updateProj! body.val
      mode.mkResultM expr (inferType expr)
  | .sort level =>
      return .mk e (.sort level.succ)
  | .const name levels =>
      mode.mkResultM e do
        let info ← getConstVal name
        return info.instantiateTypeLevelParams levels
  | .fvar fvarId =>
      mode.mkResultM e do
        let decl ← fvarId.getDecl
        return decl.type
  | .mvar mvarId =>
      mode.mkResultM e do
        let decl ← mvarId.getDecl
        return decl.type
  | .lit value =>
      return .mk e value.type
  | .bvar _ =>
      throwError "unexpected loose bound variable"

partial def transformApp (mode : TypeMode) (e : Expr) : m (mode.Result Expr) :=
  e.withApp fun fn args =>
    if let fn'@(.const name _) := fn.cleanupAnnotations then
      if let some onConstApp := onConstApp? name then
        onConstApp mode fn' args
      else
        transformAppDefault mode fn args
    else
      transformAppDefault mode fn args

partial def transformAppDefault (mode : TypeMode) (fn : Expr) (args : Array Expr) :
    m (mode.Result Expr) := do
  let fn ← transform .synth fn
  transformAppArgs mode fn.val args fn.typeAbs fn.typeEnv 0

partial def transformAppArgs (mode : TypeMode) (fn : Expr) (args : Array Expr)
    (fnTypeAbs : Expr) (fnTypeEnv : Array Expr) (i : Nat) : m (mode.Result Expr) := do
  if h : i < args.size then
    let (.forallE _ domain body _, env) ← view Expr.isForall fnTypeAbs fnTypeEnv
      | throwError "forall expected"
    let arg ← transform (.expect domain env) args[i]
    transformAppArgs mode (mkApp fn arg) args body (env.push arg) (i + 1)
  else
    return .mk fn fnTypeAbs fnTypeEnv

partial def transformForall (mode : TypeMode) (e : Expr) (fvars : Array Expr) :
    m (mode.Result Expr) := do
  match e with
  | .forallE name domain body bi =>
      let domain ← transform .synth (domain.instantiateRev fvars)
      withLocalDecl name bi domain.val fun x => do
        let body ← transformForall mode body (fvars.push x)
        match mode with
        | .expect .. =>
          return body
        | .synth =>
          let level ← domain.sortLevel!
          let bodyLevel ← body.sortLevel!
          return { body with typeAbs := .sort (mkLevelIMax' level bodyLevel) }
  | body =>
      let body ← transform .synth (body.instantiateRev fvars)
      let expr ← mkForallFVars fvars body.val
      mode.mkResultM expr do
        let bodyLevel ← body.sortLevel!
        return .sort bodyLevel

partial def transformLambdaLet (mode : TypeMode) (e : Expr) (fvars : Array Expr) :
    m (mode.Result Expr) := do
  match e with
  | .lam name domain body bi =>
      match mode with
      | .expect expectedTypeAbs expectedTypeEnv =>
          let (.forallE _ expectedDomain expectedBody _ , expectedTypeEnv) ←
            view Expr.isForall expectedTypeAbs expectedTypeEnv
            | throwError "forall expected"
          let type := instantiate expectedDomain expectedTypeEnv
          withLocalDecl name bi type fun x =>
            transformLambdaLet
              (.expect expectedBody (expectedTypeEnv.push x)) body (fvars.push x)
      | .synth =>
          let type ← transform .synth (domain.instantiateRev fvars)
          withLocalDecl name bi type.val fun x =>
            transformLambdaLet .synth body (fvars.push x)
  | .letE name domain value body nondep =>
      let type ← transform .synth (domain.instantiateRev fvars)
      let value ← transform (.expect type.val #[]) (value.instantiateRev fvars)
      withLetDecl name type.val value (nondep := nondep) fun x =>
        transformLambdaLet mode body (fvars.push x)
  | body =>
      let body ← transform mode (body.instantiateRev fvars)
      match mode with
      | .expect .. =>
          mkLambdaFVars fvars body
            (usedLetOnly := false) (generalizeNondepLet := false)
      | .synth =>
          let expr ← mkLambdaFVars fvars body.val
            (usedLetOnly := false) (generalizeNondepLet := false)
          let type ← mkForallFVars fvars body.type
            (usedLetOnly := false) (generalizeNondepLet := false)
          return .mk expr type

end

end TypedTransform

end

end TMeta.Elab
