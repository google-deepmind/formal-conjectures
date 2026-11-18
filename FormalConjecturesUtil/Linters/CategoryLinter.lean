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
def checkNotOpenIfSorryFree (mods : TSyntax ``Lean.Parser.Command.declModifiers)
    (declId : Syntax) : CommandElabM Unit := do
  -- `Lean.Elab.expandDeclId` is the natural thing to reach for here, but it calls
  -- `applyVisibility`, which throws `already been declared` once the declaration exists, and a
  -- linter runs after that. `expandDeclIdCore` is the pure part of it: it accepts the
  -- bare-identifier form of `declId`, which indexing `declId[0]` does not. The `_root_` and
  -- `private` cases are then handled the way `mkDeclName` handles them, the second being where
  -- the repository's categorised `private` declarations used to be missed.
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
  unless (← ProblemAttributes.getTags).any
      (fun t => t.declName == declName && t.category == .research .open) do return
  let some asyncInfo := (← getEnv).findAsync? declName | return
  if asyncInfo.toConstantInfo.value? (allowOpaque := true) |>.any (!·.hasSorry) then
    logLintIf linter.style.category_attribute declId
      "If a problem has a sorry-free proof, it should not be categorised as `open`."

/-- Warns unless `a` carries exactly one category attribute. Returns whether it does, so the
caller can go on to the checks that need one. `stx` is only used to place a warning when the
modifiers carry no attribute list to point at. -/
def checkExactlyOneCategory (a : TSyntax ``Lean.Parser.Command.declModifiers) (stx : Syntax) :
    CommandElabM Bool := do
  let prob_status ← toCategory a
  let outStx := match a with
  | `(declModifiers| $(_)? $atts $(_)? $(_)? $(_)? $(_)?) => atts.raw
  | _ => stx
  if prob_status.size > 1 then
    logLintIf linter.style.category_attribute outStx
      "Duplicate category attribute. There should be only one category attribute per declaration"
    return false
  if prob_status.size == 0 then
    logLintIf linter.style.category_attribute outStx
      "Missing problem category attribute"
    return false
  return true

/-- The problem category linter checks that every theorem/lemma/example
has been given a problem category attribute. -/
def categoryLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $declId:declId $_:declSig $_:declVal)
      | `(command| $a:declModifiers lemma $declId:declId $_:declSig $_:declVal) =>
        if ← checkExactlyOneCategory a stx then checkNotOpenIfSorryFree a declId
      -- An `example` has no name to look a proof up under, so only the attribute check
      -- applies to it.
      | `(command| $a:declModifiers example $_:optDeclSig $_:declVal) =>
        discard <| checkExactlyOneCategory a stx
      -- Definitions are not required to carry a category, so they are not part of the
      -- attribute check, but seven of them do carry one and the sorry-free check applied to
      -- them when it lived in the attribute. It is the case that used to work, in fact.
      | `(command| $a:declModifiers def $declId:declId $_:optDeclSig $_:declVal) =>
        checkNotOpenIfSorryFree a declId
      | _ => return

initialize do
  addLinter categoryLinter

end CategoryLinter
