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


/-! # The AMS Linter

The `AMSLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that results in a file have
the appropriate tags in order to distinguish between open/already solved
problems and background results/sanity checks.
-/

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

/-- Checks if a command has the `AMS` attribute. -/
private def toAMS
  (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntaxArray `num) := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.filterMapM fun att ↦ do
      match att with
      | `(attrInstance | AMS $nums*) => return some nums
      | _ => return none
  | _ => return #[]


/-- The problem category linter checks that every theorem/lemma/example
has been given an `AMS` attribute. -/
def AMSLinter : Linter where
  run := fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers lemma $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers example $_:bracketedBinder* : $_ := $_) =>
        let prob_status ← toAMS a
        if prob_status.flatten.isEmpty then
          logWarningAt stx "Missing AMS attribute"
          return
        if prob_status.size != 1 then logWarningAt stx "The problem should have only one AMS attribute"
      | _ => return

initialize do
  addLinter AMSLinter
