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


/-! # The Problem Status Linter

The `problemStatusLinter` is a linter to aid with formatting contributions to
the Formal Conjectures repository by ensuring that results in a file have
the appropriate tags in order to distinguish between open/already solved
problems and background results/sanity checks.
-/

open Lean Elab Meta Linter Command Parser Term

/-- Checks if a command has the `category` attribute. -/
private def toCategory
  (stx : TSyntax ``Command.declModifiers) :
    CommandElabM (Array <| TSyntax ``attrInstance) := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.filterM fun att ↦ do
      match att with
      | `(attrInstance | category $_) => return true
      | _ => return false
  | _ => return #[]

/-- The problem category linter checks that every theorem/lemma/example
has been given a problem category attribute. -/
def problemStatusLinter : Linter where
  run := fun stx => do
    match stx with
      | `(command| $a:declModifiers theorem $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers lemma $_ $_:bracketedBinder* : $_ := $_)
      | `(command| $a:declModifiers example $_:bracketedBinder* : $_ := $_) =>
        let prob_status ← toCategory a
        if prob_status.size == 0 then
          let outStx := match a with
          | `(declModifiers| $(_)? $atts $(_)? $(_)? $(_)? $(_)?) => atts.raw
          | _ => stx
          logWarningAt outStx "Missing problem category attribute"
      | _ => return

initialize do
  addLinter problemStatusLinter
