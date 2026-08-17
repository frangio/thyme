module

public import Lean.Structure
public import Lean.Data.LBool
public import Lean.Meta.Basic

open Lean Meta

namespace Thyme.Elab.TypedOpTransform

public abbrev TypeChangedFVarSet := FVarIdHashSet

def isFVarTypeChanged [Monad m] [MonadStateOf TypeChangedFVarSet m]
    (fvarId : FVarId) : m Bool :=
  return (← get).contains fvarId

@[inline]
def withFVarTypeChanged [Monad m] [MonadControlT MetaM m]
    [MonadStateOf TypeChangedFVarSet m] [MonadFinally m]
    (isTypeChanged : Bool) (k : Expr → m α) (x : Expr) : m α := do
  if isTypeChanged then
    let fvarId := x.fvarId!
    modify (·.insert fvarId)
    try k x finally modify (·.erase fvarId)
  else
    k x

@[inline]
def withLocalDecl' [Monad m] [MonadControlT MetaM m]
    [MonadStateOf TypeChangedFVarSet m] [MonadFinally m]
    (name : Name) (bi : BinderInfo) (type : Expr) (isTypeChanged : Bool)
    (k : Expr → m α) : m α :=
  withLocalDecl name bi type
    (withFVarTypeChanged isTypeChanged k)

@[inline]
def withLetDecl' [Monad m] [MonadControlT MetaM m]
    [MonadStateOf TypeChangedFVarSet m] [MonadFinally m]
    (name : Name) (type value : Expr) (isTypeChanged : Bool)
    (k : Expr → m α) (nondep : Bool := false) : m α :=
  withLetDecl name type value (nondep := nondep)
    (withFVarTypeChanged isTypeChanged k)

public section

abbrev ChangeRange := Nat

def ChangeRange.push (changeRange : ChangeRange) (isChanged : Bool) : ChangeRange :=
  if changeRange > 0 then
    if isChanged then 1 else changeRange + 1
  else
    0

/--
An expression together with an environment for its loose bound variables, with
change tracking relative to its source expression. Uses reverse instantiation,
so `bvar i` becomes `env[env.size - 1 - i]`.

Let the positions `0, ..., env.size` represent the parts on which the closure
may depend: position `0` represents `abs` itself, and position `i + 1`
represents `bvar i`. The dependency range of the closure is therefore
`[0, abs.looseBVarRange + 1)`.

The field `changeRange` partitions these positions: positions below
`changeRange` are known to be unchanged, while positions at or above it may
have changed. The closure may have changed exactly when the dependency and
change ranges overlap, equivalently when `changeRange ≤ abs.looseBVarRange`.
-/
structure Closure where
  abs : Expr
  env : Array Expr
  changeRange : ChangeRange := env.size + 1

namespace Closure

def ofExpr (e : Expr) (isChanged : Bool) : Closure where
  abs := e
  env := #[]
  changeRange := if isChanged then 0 else 1

def ofChangedExpr (e : Expr) : Closure :=
  .ofExpr e true

def ofUnchangedExpr (e : Expr) : Closure :=
  .ofExpr e false

def isChanged (clo : Closure) : Bool :=
  clo.changeRange ≤ clo.abs.looseBVarRange

def instantiate (clo : Closure) : Expr :=
  clo.abs.instantiateRev clo.env

def view (clo : Closure) (p : Expr → Bool) : MetaM Closure := do
  if p clo.abs then
    return clo
  else
    return .ofExpr (← whnf clo.instantiate) clo.isChanged

/--
Given a forall closure, invokes `k` with its domain closure and a function that
constructs its body closure from an argument and whether that argument changed.
The domain and constructed body closures do not retain the original environment
when their expressions do not depend on it.
-/
@[inline]
def withForall! [Monad m] [MonadError m] [MonadLiftT MetaM m]
    (clo : Closure)
    (k : Closure → (Expr → Bool → Closure) → m α) : m α := do
  let ⟨.forallE _ domain body _, env, changeRange⟩ ← clo.view Expr.isForall
    | throwError "forall expected"
  let domain :=
    if domain.hasLooseBVars then
      ⟨domain, env, changeRange⟩
    else
      ⟨domain, #[], min changeRange 1⟩
  let (bodyEnv, bodyChangeRange) :=
    if body.looseBVarRange > 1 then
      (env, changeRange)
    else
      (#[], min changeRange 1)
  k domain fun arg isArgChanged =>
    if body.hasLooseBVars then
      ⟨body, bodyEnv.push arg, bodyChangeRange.push isArgChanged⟩
    else
      ⟨body, bodyEnv, bodyChangeRange⟩

def sortLevel! (clo : Closure) : MetaM Level := do
  let ⟨.sort level, _, _⟩ ← clo.view Expr.isSort
    | throwError "sort expected"
  return level

end Closure

structure TypedResult (α : Type u) where
  val : α
  type : Closure

inductive TypingDir where
  | check
  | synth

namespace TypingDir

@[expose]
def Input (dir : TypingDir) : Type :=
  match dir with
  | .check => Closure
  | .synth => Unit

def Input.toOption : {dir : TypingDir} → dir.Input → Option Closure
  | .check, expected => some expected
  | .synth, _ => none

@[expose]
def Result (dir : TypingDir) (α : Type u) : Type u :=
  match dir with
  | .check => α
  | .synth => TypedResult α

namespace Result

@[expose, macro_inline]
def mk (val : α) (type : Closure) : {dir : TypingDir} → dir.Result α
  | .check => val
  | .synth => { val, type }

def val {dir : TypingDir} (result : dir.Result α) : α :=
  match dir with
  | .check => result
  | .synth => TypedResult.val result

def type {dir : TypingDir} (result : dir.Result α) (expected : dir.Input) : Closure :=
  match dir with
  | .check => expected
  | .synth => TypedResult.type result

def map (f : α → β) {dir : TypingDir} (a : dir.Result α) : dir.Result β :=
  match dir with
  | .check => f a
  | .synth => { a with val := f a.val }

end Result

end TypingDir

abbrev Coerce (m : Type → Type) :=
  (e : Expr) → (sourceType targetType : Closure) → m Expr

@[expose, macro_inline]
def coeResult [Monad m] (coerce : Coerce m)
    {dir : TypingDir} (expected : dir.Input)
    (e : Expr) (type : Closure) : m (dir.Result Expr) :=
  match dir with
  | .check =>
    if type.isChanged || expected.isChanged then
      coerce e type expected
    else
      return e
  | .synth =>
    return ⟨e, type⟩

@[expose, macro_inline]
def coeResultM [Monad m] (coerce : Coerce m)
    {dir : TypingDir} (expected : dir.Input)
    (e : Expr) (isTypeChanged : Bool) (type : m Expr) : m (dir.Result Expr) :=
  match dir with
  | .check => do
    if isTypeChanged || expected.isChanged then
      coerce e (.ofExpr (← type) isTypeChanged) expected
    else
      return e
  | .synth => do
    return ⟨e, .ofExpr (← type) isTypeChanged⟩

end

@[inline]
private unsafe def isEqualImpl (a b : Expr) : LBool :=
  if ptrEq a b then .true else .undef

/-- Returns whether its arguments are equal, or `.undef` when this is not known. -/
@[implemented_by isEqualImpl]
public def isEqual (a b : Expr) : LBool :=
  a.equal b |>.toLBool

/--
Returns the result type of a projection function after removing its structure
parameter and `self` binders.
-/
def getProjectionResultType [Monad m] [MonadEnv m] [MonadError m]
    (structName : Name) (idx : Nat) : m Expr := do
  let env ← getEnv
  let structInfo := getStructureInfo env structName
  let some projName := structInfo.getProjFn? idx | unreachable!
  let some projInfo := env.getProjectionFnInfo? projName | unreachable!
  let projType := (← getConstVal projName).type
  return projType.getForallBodyMaxDepth (projInfo.numParams + 1)

/--
Decomposes an application into its head and its application nodes, ordered
from outermost to innermost.
-/
@[inline]
def withAppSpine (e : Expr) (k : Expr → Array Expr → α) : α :=
  go e (.emptyWithCapacity e.getAppNumArgs)
where
  go (e : Expr) (apps : Array Expr) : α :=
    match e with
    | .app fn _ => go fn (apps.push e)
    | fn => k fn apps

/--
Instantiates an expression with `fvars`, applies `f` to it, and reabstracts the
value in the result. Passes the result, its abstracted value, and whether either
it or one of the binders on which it depends may have changed to `k`. If the
value is known to be unchanged, passes the original abstract expression to `k`.
-/
@[inline]
def mapUnderBinders
    [Monad m] [MonadLiftT MetaM m]
    {dir : TypingDir}
    (expr : Expr) (fvars : Array Expr) (changeRange : ChangeRange)
    (f : Expr → m (dir.Result Expr))
    (k : dir.Result Expr → Expr → Bool → m α) : m α := do
  let inst := expr.instantiateRev fvars
  let result ← f inst
  let equal := isEqual inst result.val
  let isChanged := equal != .true || changeRange ≤ expr.looseBVarRange
  if equal == .true then
    k result expr isChanged
  else
    k result (← result.val.abstractM fvars) isChanged

public inductive OpAppTransform (m : Type → Type) where
  | default
  | transform {n : Nat} (onOpApp :
      (dir : TypingDir) → dir.Input →
      (fn : Expr) → (args : Vector Expr n) → m (dir.Result Expr))
  deriving Inhabited

variable (getOpAppTransform : Name → OpAppTransform m) (coerce : Coerce m)

variable [Monad m] [MonadEnv m] [MonadError m] [MonadFinally m]
  [MonadLiftT MetaM m] [MonadControlT MetaM m]
  [MonadStateOf TypeChangedFVarSet m]

local instance [MonadExceptOf Exception m] : Nonempty (m α) :=
  ⟨throw default⟩

mutual

public partial def transform (dir : TypingDir) (expected : dir.Input) (e : Expr) :
    m (dir.Result Expr) := do
  match e with
  | .app .. =>
    transformApp dir expected e
  | .lam .. | .letE .. =>
    transformLambdaLet dir expected e #[] 1
  | .forallE .. =>
    transformForall dir expected e #[] 1
  | .mdata _ body =>
    let body ← transform dir expected body
    return body.map e.updateMData!
  | .proj .. =>
    transformProj dir expected e
  | .sort level =>
    coeResultM coerce expected e false (return (.sort level.succ))
  | .const name levels =>
    coeResultM coerce expected e false do
      let info ← getConstVal name
      return info.instantiateTypeLevelParams levels
  | .fvar fvarId =>
    let isTypeChanged ← isFVarTypeChanged fvarId
    coeResultM coerce expected e isTypeChanged do
      let decl ← fvarId.getDecl
      return decl.type
  | .lit value =>
    coeResultM coerce expected e false (return value.type)
  | .mvar _ =>
    throwError "unexpected metavariable"
  | .bvar _ =>
    throwError "unexpected loose bound variable"

partial def transformProj (dir : TypingDir) (expected : dir.Input)
    (e : Expr) : m (dir.Result Expr) := do
  let .proj structName idx sourceStruct := e | throwError "projection expected"
  let struct ← transform .synth () sourceStruct
  let e := e.updateProj! struct.val
  let structType := struct.type ()
  let isStructValChanged := isEqual sourceStruct struct.val != .true
  let projResultType ← getProjectionResultType structName idx
  let isTypeChanged :=
    (isStructValChanged && projResultType.hasLooseBVar 0) ||
    (structType.isChanged && projResultType.hasLooseBVars)
  coeResultM coerce expected e isTypeChanged (inferType e)

partial def transformApp (dir : TypingDir) (expected : dir.Input) (e : Expr) :
    m (dir.Result Expr) :=
  withAppSpine e fun fn apps =>
    if let fn'@(.const name _) := fn.cleanupAnnotations then
      match getOpAppTransform name with
      | .default =>
        transformAppDefault dir expected fn apps
      | .transform onOpApp (n := n) =>
        let args := apps.map (·.appArg!)
        if h : n ≤ args.size then do
          let opArgs := .ofFn fun i => args[args.size - 1 - i]
          if n = args.size then
            onOpApp dir expected fn' opArgs
          else
            let fn ← onOpApp .synth () fn' opArgs
            transformAppArgs dir expected fn.val (fn.type ()) apps
              ⟨apps.size - n, by omega⟩
        else
          throwError "operator '{name}' expected at least {n} arguments, got {apps.size}"
    else
      transformAppDefault dir expected fn apps

partial def transformAppDefault (dir : TypingDir) (expected : dir.Input)
    (fn : Expr) (apps : Array Expr) : m (dir.Result Expr) := do
  let fn ← transform .synth () fn
  transformAppArgs dir expected fn.val (fn.type ()) apps
    ⟨apps.size, by omega⟩

partial def transformAppArgs (dir : TypingDir) (expected : dir.Input)
    (fn : Expr) (fnType : Closure) (apps : Array Expr)
    (rem : Fin (apps.size + 1)) : m (dir.Result Expr) := do
  match rem with
  | ⟨0, _⟩ =>
    coeResult coerce expected fn fnType
  | ⟨rem + 1, hrem⟩ =>
    let app := apps[rem]
    fnType.withForall! fun domain body => do
      let sourceArg := app.appArg!
      let arg ← transform .check domain sourceArg
      let isArgChanged := isEqual sourceArg arg != .true
      let fn := app.updateApp! fn arg
      transformAppArgs dir expected fn (body arg isArgChanged) apps ⟨rem, by omega⟩

partial def transformLambdaLet (dir : TypingDir) (expected : dir.Input)
    (e : Expr) (fvars : Array Expr) (changeRange : ChangeRange) : m (dir.Result Expr) := do
  match e with
  | .lam name sourceDomain body bi =>
    match dir with
    | .check =>
      expected.withForall! fun domain bodyType =>
        mapUnderBinders (dir := .check) sourceDomain fvars changeRange
          (fun _ => pure domain.instantiate)
          fun domainVal domainAbs isDomainChanged =>
            let isDomainChanged := isDomainChanged || domain.isChanged
            withLocalDecl' name bi domainVal isDomainChanged fun x => do
              let body ← transformLambdaLet .check
                (bodyType x isDomainChanged) body (fvars.push x) (changeRange.push isDomainChanged)
              return e.updateLambdaE! domainAbs body
    | .synth =>
      mapUnderBinders sourceDomain fvars changeRange
        (transform .synth ())
        fun domain domainAbs isDomainChanged =>
          withLocalDecl' name bi domain.val isDomainChanged fun x => do
            let body ← transformLambdaLet .synth () body (fvars.push x) (changeRange.push isDomainChanged)
            return body.map (e.updateLambdaE! domainAbs)
  | .letE name sourceDomain sourceValue body nondep =>
    mapUnderBinders sourceDomain fvars changeRange
      (transform .synth ())
      fun domain domainAbs isDomainChanged =>
        mapUnderBinders sourceValue fvars changeRange
          (transform .check (.ofExpr domain.val isDomainChanged))
          fun value valueAbs isValueChanged =>
            let isBinderChanged := isDomainChanged || isValueChanged
            withLetDecl' name domain.val value isDomainChanged (nondep := nondep) fun x => do
              let body ← transformLambdaLet dir expected body (fvars.push x) (changeRange.push isBinderChanged)
              return body.map (e.updateLetE! domainAbs valueAbs)
  | body =>
    mapUnderBinders body fvars changeRange
      (transform dir expected)
      fun body bodyAbs _ => do
        match dir with
        | .check =>
          return bodyAbs
        | .synth =>
          let bodyType := body.type ()
          let type ← mkForallFVars fvars bodyType.instantiate
            (usedLetOnly := false) (generalizeNondepLet := false)
          let isTypeChanged := bodyType.isChanged || changeRange ≤ fvars.size
          return ⟨bodyAbs, (.ofExpr type isTypeChanged)⟩

partial def transformForall (dir : TypingDir) (expected : dir.Input)
    (e : Expr) (fvars : Array Expr) (changeRange : ChangeRange) : m (dir.Result Expr) := do
  match e with
  | .forallE name sourceDomain body bi =>
    mapUnderBinders sourceDomain fvars changeRange
      (transform .synth ())
      fun domain domainAbs isDomainChanged =>
        withLocalDecl' name bi domain.val isDomainChanged fun x => do
          let body ← transformForall dir expected body (fvars.push x) (changeRange.push isDomainChanged)
          let expr := e.updateForallE! domainAbs body.val
          let domainType := domain.type ()
          let bodyType := body.type expected
          let isTypeChanged := domainType.isChanged || bodyType.isChanged
          coeResultM coerce expected expr isTypeChanged do
            let domainLevel ← domainType.sortLevel!
            let bodyLevel ← bodyType.sortLevel!
            return .sort (mkLevelIMax' domainLevel bodyLevel)
  | body =>
    mapUnderBinders body fvars changeRange (transform .synth ())
      fun body bodyAbs _ => return .mk bodyAbs (body.type ())

end

end Thyme.Elab.TypedOpTransform
