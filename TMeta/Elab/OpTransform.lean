module

public import Lean.Meta.Basic

open Lean Meta

namespace TMeta.Elab.OpTransform

/--
Decomposes an application into its head and its application nodes, ordered
from outermost to innermost.
-/
@[inline]
def withAppSpine (e : Expr) (k : Expr → Array Expr → α) : α :=
  go e #[]
where
  go (e : Expr) (apps : Array Expr) : α :=
    match e with
    | .app fn _ => go fn (apps.push e)
    | fn => k fn apps

@[inline]
private unsafe def mapUnderBinders!Impl [Monad m] [MonadLiftT MetaM m]
    (expr : Expr) (fvars : Array Expr)
    (f : Expr → m Expr) (k : Expr → Expr → m α) : m α := do
  let inst := expr.instantiateRev fvars
  let result ← f inst
  if ptrEq inst result then
    k inst expr
  else
    k inst (← result.abstractM fvars)

/--
Instantiates an expression with `fvars`, applies `f` to it, and abstracts the
result again. Passes the instantiated expression and the abstracted result to
`k`. If `f` returns a pointer-equal result, the runtime implementation also
returns a pointer-equal abstracted result.
-/
@[implemented_by mapUnderBinders!Impl]
def mapUnderBinders! [Monad m] [MonadLiftT MetaM m]
    (expr : Expr) (fvars : Array Expr)
    (f : Expr → m Expr) (k : Expr → Expr → m α) : m α := do
  let inst := expr.instantiateRev fvars
  k inst (← (← f inst).abstractM fvars)

public section

inductive OpAppTransform (m : Type → Type) where
  | default
  | skip (n : Nat)
  | transform {n : Nat} (onOpApp : (fn : Expr) → (args : Vector Expr n) → m Expr)
  deriving Inhabited

variable [Monad m] [MonadError m] [MonadLiftT MetaM m] [MonadControlT MetaM m]

variable (getOpAppTransform : Name → OpAppTransform m)

mutual

partial def transform (e : Expr) : m Expr := do
  match e with
  | .app .. =>
      transformApp e
  | .lam .. | .letE .. =>
      transformLambdaLet e #[]
  | .forallE .. =>
      transformForall e #[]
  | .mdata _ body =>
      return e.updateMData! (← transform body)
  | .proj _ _ body =>
      return e.updateProj! (← transform body)
  | .sort .. | .const .. | .fvar .. | .mvar .. | .lit .. =>
      return e
  | .bvar _ =>
      throwError "unexpected loose bound variable"

partial def transformApp (e : Expr) : m Expr :=
  withAppSpine e fun fn apps =>
    if let fn'@(.const name _) := fn.cleanupAnnotations then
      match getOpAppTransform name with
      | .default =>
          transformAppDefault fn apps
      | .skip n =>
          if hu : n ≤ apps.size then do
            let fn := if hl : n = 0 then fn else apps[apps.size - n]
            transformAppArgs fn apps (apps.size - n)
          else
            throwError "operator '{name}' expected at least {n} arguments, got {apps.size}"
      | .transform onOpApp (n := n) =>
          let args := apps.map (·.appArg!)
          if h : n ≤ args.size then do
            let fn ← onOpApp fn' (.ofFn fun i => args[args.size - 1 - i])
            args.foldrM (init := fn) (start := args.size - n) fun app fn => do
              return .app fn (← transform app)
          else
            throwError "operator '{name}' expected at least {n} arguments, got {apps.size}"
    else
      transformAppDefault fn apps

partial def transformAppDefault (fn : Expr) (apps : Array Expr) : m Expr := do
  let fn ← transform fn
  transformAppArgs fn apps apps.size

partial def transformAppArgs (fn : Expr) (apps : Array Expr) (size : Nat) : m Expr :=
  apps.foldrM (init := fn) (start := size) fun app fn => do
    let arg ← transform app.appArg!
    return app.updateApp! fn arg

partial def transformLambdaLet (e : Expr) (fvars : Array Expr) : m Expr := do
  match e with
  | .lam name domain body bi =>
      mapUnderBinders! domain fvars transform fun instDomain domain =>
        withLocalDecl name bi instDomain fun x => do
          let body ← transformLambdaLet body (fvars.push x)
          return e.updateLambdaE! domain body
  | .letE name domain value body nondep =>
      mapUnderBinders! domain fvars transform fun instDomain domain =>
        mapUnderBinders! value fvars transform fun instValue value =>
          withLetDecl name instDomain instValue (nondep := nondep) fun x => do
            let body ← transformLambdaLet body (fvars.push x)
            return e.updateLetE! domain value body
  | body =>
      mapUnderBinders! body fvars transform fun _ body =>
        return body

partial def transformForall (e : Expr) (fvars : Array Expr) : m Expr := do
  match e with
  | .forallE name domain body bi =>
      mapUnderBinders! domain fvars transform fun instDomain domain =>
        withLocalDecl name bi instDomain fun x => do
          let body ← transformForall body (fvars.push x)
          return e.updateForallE! domain body
  | body =>
      mapUnderBinders! body fvars transform fun _ body =>
        return body

end

end

end TMeta.Elab.OpTransform
