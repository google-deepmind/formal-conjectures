/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesForMathlib.Tactic.Linter.Term
import Mathlib

open Lean Meta

namespace ExistsImplicationLinter

register_option linter.style.existsImplication : Bool := {
  defValue := true
  descr := "Detects misformalisations caused by writing ∃ x, P x → Q rather than ∃ x, P x ∧ Q "
}

def forallToAnd (expr : Expr) : MetaM Expr :=
  forallTelescope expr fun vars final => do
    let varsAsProp ← vars.mapM inferType
    varsAsProp.foldrM (fun var currentBigAnd =>
      mkAppM ``And #[var, currentBigAnd]) final

/--
Checks if an expression contains the pattern `∃ x, P x → Q`.
-/
partial def checkExistsArrow (stx : Syntax) (e : Expr) : MetaM Unit := do
  match e with
  | .mdata _ e => checkExistsArrow stx e
  | .app .. =>
      -- Check if this is an application of `Exists`
      if e.isAppOfArity ``Exists 2 then
        let lam := e.getAppArgs[1]!
        let .lam _ _ target _ := lam
          | throwError m!"Encountered an ill-formed existential expression {e}"
        -- If the inside of the lambda expression is not a forall then we're fine.
        unless target.isForall do return
        lambdaTelescope lam fun vars target => do
          let correctCore ← forallToAnd target
          let correctLam ← Lean.Meta.mkLambdaFVars vars correctCore
          let suggestedExpr ← mkAppM ``Exists #[correctLam]
          Lean.Linter.logLintIf linter.style.existsImplication stx
              m!"Declaration contains the pattern the expression {e}. \
                Did you mean {suggestedExpr}?"
  | _ => pure ()

/--
The `existsImplicationLinter` detects expressions of the form `∃ a, P a → Q` and flags them to the
user since those are rarely correct.
-/
def existsImplicationLinter : Linter where
  -- TODO(Paul-Lez): Running in `StateT Unit MetaM Unit` is a bit of a hack.
  -- Do this with a non-StateT version of `runTermLinter`?
  run := Lean.Elab.Command.Linter.runTermLinter (σ := Unit) linter.style.existsImplication
    fun expr stx => checkExistsArrow expr stx

initialize addLinter existsImplicationLinter

end ExistsImplicationLinter
