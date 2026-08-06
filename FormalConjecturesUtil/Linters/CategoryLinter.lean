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

public import FormalConjecturesUtil.Attributes.Basic
public import Mathlib.Tactic.Lemma


/-! # The Category Linter

The `categoryLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that results in a file have
the appropriate tags in order to distinguish between open/already solved
problems and background results/sanity checks.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.category_attribute : Bool := {
  defValue := false
  descr := "enable the `category` attribute style linter"
}

-- FIXME: False positive
set_option linter.style.docString.empty false

namespace CategoryLinter

/-- Checks if a command has the `category` attribute. -/
def toCategory
  (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntax ``attrInstance) := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.filterM fun att ↦ do
      match att with
      | `(attrInstance | category $_) => return true
      | _ => return false
  | _ => return #[]

/-- Warns when a problem categorised as `research open` turns out to have a sorry-free proof.

This check used to live in the `category` attribute, at `.afterTypeChecking`, where it never fired
for a theorem: proof terms elaborate asynchronously, so `value?` was still `none`. It did fire for
a `def`, which is why the gap went unnoticed.

`.afterCompilation` is late enough to see the proof term in an ordinary file, but not inside a
module, and every file in `FormalConjecturesTest` is a module. An attribute-based check therefore
cannot be given a test. A linter runs once the command has finished and works in both, so the
check lives here and `findAsync?` waits on the elaboration task. -/
def checkNotOpenIfSorryFree (declId : Syntax) : CommandElabM Unit := do
  let declName := (← getCurrNamespace) ++ declId[0].getId
  unless ← hasConst declName do return
  unless (← ProblemAttributes.getTags).any
      (fun t => t.declName == declName && t.category == .research .open) do return
  let some asyncInfo := (← getEnv).findAsync? declName | return
  if asyncInfo.toConstantInfo.value?.any (!·.hasSorry) then
    logLintIf linter.style.category_attribute declId
      "If a problem has a sorry-free proof, it should not be categorised as `open`."

/-- The problem category linter checks that every theorem/lemma/example
has been given a problem category attribute. -/
def categoryLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers lemma $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers example $_:bracketedBinder* : $_ := $_) =>
        let prob_status ← toCategory a
        let outStx := match a with
        | `(declModifiers| $(_)? $atts $(_)? $(_)? $(_)? $(_)?) => atts.raw
        | _ => stx
        if prob_status.size > 1 then
          logLintIf linter.style.category_attribute outStx
            "Duplicate category attribute. There should be only one category attribute per declaration"
          return
        if prob_status.size == 0 then
          logLintIf linter.style.category_attribute outStx
            "Missing problem category attribute"
          return
        match stx with
          | `(command| $_:declModifiers theorem $declId:declId $_:declSig $_:declVal)
          | `(command| $_:declModifiers lemma $declId:declId $_:declSig $_:declVal) =>
            checkNotOpenIfSorryFree declId
          | _ => return
      | _ => return

initialize do
  addLinter categoryLinter

end CategoryLinter
