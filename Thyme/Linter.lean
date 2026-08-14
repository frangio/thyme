module

import Lean.Linter.Basic
import Lean.Linter.Util
import Thyme.Code

open Lean Elab Command
open Lean.Linter

namespace Thyme.Elab

register_option linter.thyme.codeTransport : Bool := {
  defValue := true
  descr := "warn about equality transport of staged code"
}

def hasStagedParameter : Expr → Bool
  | .forallE _ type body binderInfo =>
    (binderInfo == .instImplicit && type.isConstOf ``Staged) ||
      hasStagedParameter body
  | _ => false

def getTransportSourceType? (e : Expr) : Option Expr :=
  let n := e.getAppNumArgs'
  match e.getAppFn' with
  | .const name levels =>
    if name == ``Eq.mp || name == ``cast then
      if n < 1 then none else some (e.getArg!' 0 n)
    else if name == ``Eq.mpr then
      if n < 2 then none else some (e.getArg!' 1 n)
    else if name == ``Eq.ndrec || name == ``Eq.ndrecOn || name == ``Eq.ndrec_symm then
      if n < 3 then none
      else
        let source := e.getArg!' 1 n
        let motive := e.getArg!' 2 n
        some <| mkApp motive source
    else if name == ``Eq.rec || name == ``Eq.recOn || name == ``Eq.casesOn then
      if n < 3 then none
      else
        let u := levels[1]!
        let α := e.getArg!' 0 n
        let source := e.getArg!' 1 n
        let motive := e.getArg!' 2 n
        let refl := mkApp2 (mkConst ``Eq.refl [u]) α source
        some <| mkApp2 motive source refl
    else
      none
  | _ => none

def isStagedType (env : Environment) (type : Expr) : Bool :=
  match type.headBeta.consumeMData.getAppFn' with
  | .const name _ =>
    name == ``Thyme.Code ||
      (env.find? name).any fun info => hasStagedParameter info.type
  | _ => false

def isCodeTransport (env : Environment) (e : Expr) : Bool :=
  (getTransportSourceType? e).any fun type =>
    isStagedType env type

partial def findCodeTransport? (env : Environment) (e : Expr) : Option Expr :=
  e.findExt? fun e =>
    if isCodeTransport env e then .found
    else if e.getAppFn'.isConstOf ``Thyme.Code.mk then
      let n := e.getAppNumArgs'
      if 2 < n && (findCodeTransport? env (e.getArg!' 2 n)).isSome then
        .found
      else
        .done
    else .visit

def codeTransportLinter : Linter where
  run := withSetOptionIn fun stx => do
    if (← get).messages.hasErrors then
      return
    let env ← getEnv
    for tree in ← getInfoTrees do
      for declName in getDeclsByBody tree do
        let some info := env.find? declName | continue
        unless hasStagedParameter info.type do
          continue
        let some value := info.value? (allowOpaque := true) | continue
        if (findCodeTransport? env value).isSome then
          logLintIf linter.thyme.codeTransport stx
            "declaration may produce an incoherent generator: its elaborated term transports a \
              `Code` value across an equality; ensure that rewrites occur inside quotations"

initialize addLinter codeTransportLinter

end Thyme.Elab
