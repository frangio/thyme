module

public import Lean.Meta.InferType

open Lean Meta

namespace TMeta

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

structure TypedExpr where
  expr : Expr
  typeAbs : Expr
  typeEnv : Array Expr
  deriving Inhabited

def TypedExpr.type (e : TypedExpr) : Expr :=
  instantiate e.typeAbs e.typeEnv

def TypedExpr.sortLevel! (e : TypedExpr) : MetaM Level := do
  let (.sort level, _) ← view Expr.isSort e.typeAbs e.typeEnv
    | throwError "type expected"
  return level

inductive TypeMode where
  | expect (typeAbs : Expr) (typeEnv : Array Expr)
  | synth

abbrev TypeMode.Result : TypeMode → Type
  | .expect .. => Expr
  | .synth => TypedExpr

@[expose, macro_inline]
def TypeMode.mkResult (expr typeAbs : Expr) (typeEnv : Array Expr := #[]) :
    (mode : TypeMode) → mode.Result
  | .expect .. => expr
  | .synth => { expr, typeAbs, typeEnv }

@[expose, macro_inline]
def TypeMode.mkResultM [Monad m] (expr : Expr) (type : m Expr) :
    (mode : TypeMode) → m mode.Result
  | .expect .. => return expr
  | .synth => return { expr, typeAbs := ← type, typeEnv := #[] }

abbrev ConstAppTransform (m : Type → Type) :=
  (mode : TypeMode) → (fn : Expr) → (args : Array Expr) → m mode.Result

abbrev GetConstAppTransform? (m : Type → Type) :=
  Name → Option (ConstAppTransform m)

variable [Monad m] [MonadEnv m] [MonadError m]
  [MonadLiftT MetaM m] [MonadControlT MetaM m]

local instance [MonadExceptOf Exception m] : Nonempty (m α) :=
  ⟨throw default⟩

namespace Transform

variable (onConstApp? : GetConstAppTransform? m)

mutual

partial def transform (mode : TypeMode) (e : Expr) : m mode.Result := do
  match e with
  | .app .. =>
      transformApp mode e
  | .lam .. | .letE .. =>
      transformLambdaLet mode e #[]
  | .forallE .. =>
      transformForall mode e #[]
  | .mdata _ body =>
      let body ← transform mode body
      match mode with
      | .expect .. =>
          return e.updateMData! body
      | .synth =>
          return { body with expr := e.updateMData! body.expr }
  | .proj _ _ body =>
      let body ← transform .synth body
      let expr := e.updateProj! body.expr
      mode.mkResultM expr (inferType expr)
  | .sort level =>
      return mode.mkResult e (.sort level.succ)
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
      return mode.mkResult e value.type
  | .bvar _ =>
      throwError "unexpected loose bound variable"

partial def transformApp (mode : TypeMode) (e : Expr) : m mode.Result :=
  e.withApp fun fn args =>
    if let fn'@(.const name _) := fn.cleanupAnnotations then
      if let some onConstApp := onConstApp? name then
        onConstApp mode fn' args
      else
        transformAppDefault mode fn args
    else
      transformAppDefault mode fn args

partial def transformAppDefault (mode : TypeMode) (fn : Expr) (args : Array Expr) :
    m mode.Result := do
  let fn ← transform .synth fn
  transformAppArgs mode fn.expr args fn.typeAbs fn.typeEnv 0

partial def transformAppArgs (mode : TypeMode) (fn : Expr) (args : Array Expr)
    (fnTypeAbs : Expr) (fnTypeEnv : Array Expr) (i : Nat) : m mode.Result := do
  if h : i < args.size then
    let (.forallE _ domain body _, env) ← view Expr.isForall fnTypeAbs fnTypeEnv
      | throwError "forall expected"
    let arg ← transform (.expect domain env) args[i]
    transformAppArgs mode (mkApp fn arg) args body (env.push arg) (i + 1)
  else
    return mode.mkResult fn fnTypeAbs fnTypeEnv

partial def transformForall (mode : TypeMode) (e : Expr) (fvars : Array Expr) :
    m mode.Result := do
  match e with
  | .forallE name domain body bi =>
      let domain ← transform .synth (domain.instantiateRev fvars)
      withLocalDecl name bi domain.expr fun x => do
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
      let expr ← mkForallFVars fvars body.expr
      mode.mkResultM expr do
        let bodyLevel ← body.sortLevel!
        return .sort bodyLevel

partial def transformLambdaLet (mode : TypeMode) (e : Expr) (fvars : Array Expr) :
    m mode.Result := do
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
          withLocalDecl name bi type.expr fun x =>
            transformLambdaLet .synth body (fvars.push x)
  | .letE name domain value body nondep =>
      let type ← transform .synth (domain.instantiateRev fvars)
      let value ← transform (.expect type.expr #[]) (value.instantiateRev fvars)
      withLetDecl name type.expr value (nondep := nondep) fun x =>
        transformLambdaLet mode body (fvars.push x)
  | body =>
      let body ← transform mode (body.instantiateRev fvars)
      match mode with
      | .expect .. =>
          mkLambdaFVars fvars body
            (usedLetOnly := false) (generalizeNondepLet := false)
      | .synth =>
          let expr ← mkLambdaFVars fvars body.expr
            (usedLetOnly := false) (generalizeNondepLet := false)
          let type ← mkForallFVars fvars (instantiate body.typeAbs body.typeEnv)
            (usedLetOnly := false) (generalizeNondepLet := false)
          return { expr, typeAbs := type, typeEnv := #[] }

end

end Transform

end

end TMeta
