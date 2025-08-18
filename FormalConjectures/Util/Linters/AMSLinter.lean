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

import FormalConjectures.Util.Attributes
import Mathlib.Tactic.Lemma
import Batteries.Data.Array.Merge


/-! # The AMS Linter

The `AMSLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that results in a file have
the appropriate subject tags.
-/

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

/-- Checks if a command has the `AMS` attribute. -/
private def toAMS (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntaxArray `num) := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.filterMapM fun att ↦ do
      match att with
      | `(attrInstance | AMS $nums*) => return some nums
      | _ => return none
  | _ => return #[]

private def mkAMSSyntax (nums : TSyntaxArray `num) : CommandElabM <| TSyntax ``attrInstance := do
  return ← `(attrInstance | AMS $nums*)

/-- The problem category linter checks that every theorem/lemma/example
has been given an `AMS` attribute. -/
def AMSLinter : Linter where
  run := fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers lemma $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers example $_:bracketedBinder* : $_ := $_) =>
        let ams ← toAMS a
        let outStx := match a with
        | `(declModifiers| $(_)? $atts $(_)? $(_)? $(_)? $(_)?) => atts.raw
        | _ => stx
        if ams.size > 1 then
          let numerals := ams.flatten
          let outCorrect := m!"{← mkAMSSyntax numerals}"
          let currentOut := m!", ".joinSep (← ams.mapM fun nums ↦ do return m!"{← mkAMSSyntax nums}").toList
          logWarningAt outStx m!"The AMS tag should be formatted as {outCorrect} rather than {currentOut}"
          return
        if ams.size == 0 then
          logWarningAt outStx "Missing AMS attribute."
          return
        if ams.flatten.isEmpty then
          -- If we're here then there is at least one AMS tag, but it doesn't have any number.
          logWarningAt outStx "The AMS tag should have at least one subject number."
        -- Check there the AMS tags are sorted and do not contain duplicates
        let ams_sorted := ams.flatten.qsort (fun n m => n.getNat < m.getNat)
        if ams_sorted != ams.flatten then
          logWarningAt outStx m!"The AMS tags should be ordered as {← mkAMSSyntax ams_sorted}"
          return
        if ams_sorted.dedupSorted != ams_sorted then
          logWarningAt outStx m!"AMS tags contain duplicates. This should be {← mkAMSSyntax ams_sorted.dedupSorted}"
      | _ => return

initialize do
  addLinter AMSLinter
