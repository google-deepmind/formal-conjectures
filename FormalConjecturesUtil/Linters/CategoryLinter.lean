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
      | `(command| $a:declModifiers theorem $_:declId $_:declSig $_:declVal)
      | `(command| $a:declModifiers lemma $_:declId $_:declSig $_:declVal) =>
        discard <| checkExactlyOneCategory a stx
      -- An `example` has no name to look a proof up under, so only the attribute check
      -- applies to it.
      | `(command| $a:declModifiers example $_:optDeclSig $_:declVal) =>
        discard <| checkExactlyOneCategory a stx
      | _ => return

initialize do
  addLinter categoryLinter

end CategoryLinter
