/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public meta import FormalConjecturesUtil.Attributes.Basic
public import Mathlib.Tactic.Lemma


/-! # The Formal Proof Linter

A `conditional formal_proof` names the hypotheses its proof assumes, each stated
in the same file with a `sorry` proof. If one of those is later proved, the proof
is no longer conditional on it and the annotation should be revisited.

Noticing that means reading the hypothesis's proof term, which the attribute
cannot do from inside a module: `env.find?` returns nothing useful there, so the
check silently does nothing in exactly the files a test would live in. See #4780.
A linter can, through `findAsync?`, which is the same route `CategoryLinter` takes
for the equivalent check on `category`.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.conditional_formal_proof : Bool := {
  defValue := false
  descr := "enable the `conditional formal_proof` style linter"
}

-- FIXME: False positive
set_option linter.style.docString.empty false

namespace FormalProofLinter

/-- Whether `declName` has a proof term with no `sorry` in it, waiting on the
declaration to finish elaborating. -/
def isProved (declName : Name) : CommandElabM Bool := do
  let some info := (← getEnv).findAsync? declName | return false
  return info.toConstantInfo.value?.any (!·.hasSorry)

/-- Warns when a hypothesis assumed by a `conditional formal_proof` has since been
proved, so the proof may no longer be conditional on it. -/
def checkAssumptionsStillOpen (declId : Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ declId[0].getId
  unless ← hasConst declName do return
  for condName in ← liftTermElabM (ProblemAttributes.getProofConditions declName) do
    if ← isProved condName then
      logLintIf linter.style.conditional_formal_proof declId
        m!"The assumed hypothesis `{condName}` has a sorry-free proof, so the \
           formal proof may no longer need to be marked `conditional`."

/-- Checks the assumptions named by a `conditional formal_proof`. -/
def formalProofLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
      | `(command| $_:declModifiers theorem $declId $_:bracketedBinder* : $_ := $_)
      | `(command| $_:declModifiers lemma $declId $_:bracketedBinder* : $_ := $_) =>
        checkAssumptionsStillOpen declId
      | _ => return

initialize do
  addLinter formalProofLinter

end FormalProofLinter
