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

/-- Return every formal-proof tag attached to `declName`.

A declaration may have more than one proof. Linter policy must therefore be
computed over the complete list rather than the legacy singular accessor. -/
def getFormalProofTagsFor
    (declName : Name) : CommandElabM (Array ProblemAttributes.FormalProofTag) := do
  let tags ← liftTermElabM ProblemAttributes.getFormalProofTags
  return tags.filter (·.declName == declName)

/-- Warns when a hypothesis assumed by a `conditional formal_proof` has since been
proved, so the proof may no longer be conditional on it. -/
def checkAssumptionsStillOpen (mods : TSyntax ``Lean.Parser.Command.declModifiers) (declId : Syntax) : CommandElabM Unit := do
  let modifiers ← elabModifiers mods
  let (shortName, _) := Lean.Elab.expandDeclIdCore declId
  let declName ←
    if (`_root_).isPrefixOf shortName then
      pure <| shortName.replacePrefix `_root_ .anonymous
    else
      pure <| (← getCurrNamespace) ++ shortName
  let env ← getEnv
  let declName := if modifiers.isPrivate then mkPrivateName env declName else declName
  unless ← hasConst declName do return
  let mut seen : Std.HashSet Name := {}
  for tag in ← getFormalProofTagsFor declName do
    for condName in tag.conditions do
      unless seen.contains condName do
        seen := seen.insert condName
        if ← isProved condName then
          logLintIf linter.style.conditional_formal_proof declId
            m!"The assumed hypothesis `{condName}` has a sorry-free proof, so the \
               formal proof may no longer need to be marked `conditional`."

/-- Warns when a statement with a `formal_proof` annotation has a proof that is not exactly `sorry` or `by sorry`,
unless it is conditional. The main branch is a statement repository, so proofs should live in
their own repository or branch. -/
def checkProofIsSorryIfFormalProof (mods : TSyntax ``Lean.Parser.Command.declModifiers) (declId : Syntax) (val : TSyntax ``Lean.Parser.Command.declVal) : CommandElabM Unit := do
  let modifiers ← elabModifiers mods
  let (shortName, _) := Lean.Elab.expandDeclIdCore declId
  let declName ←
    if (`_root_).isPrefixOf shortName then
      pure <| shortName.replacePrefix `_root_ .anonymous
    else
      pure <| (← getCurrNamespace) ++ shortName
  let env ← getEnv
  let declName := if modifiers.isPrivate then mkPrivateName env declName else declName
  unless ← hasConst declName do return

  let tags ← getFormalProofTagsFor declName
  if tags.any (·.conditions.isEmpty) then
    let isSorry := match val with
      | `(Lean.Parser.Command.declVal| := by sorry) => true
      | `(Lean.Parser.Command.declVal| := sorry) => true
      | _ => false
    if !isSorry then
      logLintIf linter.style.conditional_formal_proof declId
        m!"A statement with a `formal_proof` annotation must be proved exactly `by sorry` \
           in this repository (unless it has conditionals). Proofs should live in their own repository or branch."

/-- Checks the assumptions named by a `conditional formal_proof` and ensures `formal_proof` statements are `sorry`. -/
def formalProofLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
      | `(command| $mods:declModifiers theorem $declId $_:bracketedBinder* : $_ $val:declVal)
      | `(command| $mods:declModifiers lemma $declId $_:bracketedBinder* : $_ $val:declVal) =>
        checkAssumptionsStillOpen mods declId
        checkProofIsSorryIfFormalProof mods declId val
      | _ => return

initialize do
  addLinter formalProofLinter

end FormalProofLinter
