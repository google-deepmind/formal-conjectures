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

import FormalConjectures.Util.Attributes
import Mathlib.Tactic.Lemma

open Lean Elab Meta Linter Command Parser Term

namespace ResearchOpenLinter

/-- Checks if a command has the `category research open` attribute. -/
def isResearchOpen
  (stx : TSyntax ``Command.declModifiers) :
    CommandElabM Bool := do
  match stx with
  | `(declModifiers| $(_)? @[$[$atts],*] $(_)? $(_)? $(_)? $(_)?) =>
    atts.anyM fun att ↦ do
      match att with
      | `(attrInstance | category research open) => return true
      | _ => return false
  | _ => return false

def check (mods : TSyntax ``Command.declModifiers) (body : TSyntax `term) : CommandElabM Unit := do
  if ← isResearchOpen mods then
    match body with
    | `(term| sorry) => return
    | `(term| by sorry) => return
    | _ =>
      logWarningAt body "A proof is provided for a problem categorized as `open`, should be `solved`"

/-- The research open linter checks that every research open problem is proved using 'sorry'. -/
def researchOpenLinter : Linter where
  run := fun stx => do
    match stx with
      | `(command| $mods:declModifiers theorem $_ $_:bracketedBinder* : $_ := $body) =>
        check mods body
      | `(command| $mods:declModifiers lemma $_ $_:bracketedBinder* : $_ := $body) =>
        check mods body
      | `(command| $mods:declModifiers example $_:bracketedBinder* : $_ := $body) =>
        check mods body
      | _ => return

initialize do
  addLinter researchOpenLinter

end ResearchOpenLinter
