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

import FormalConjectures.Util.Attributes.Basic
import Mathlib.Tactic.Lemma
import Batteries.Data.Array.Merge


/-! # The AnswerLinter

The `AnswerLinter` is a linter to aid with using `answer(sorry)` correctly.
-/

open Lean Elab Meta Linter Command Parser Term

register_option linter.style.answer_attribute : Bool := {
  defValue := true
  descr := "enable the `answer(sorry)` style linter"
}

namespace AnswerLinter

-- Helper to check for arguments (h : True)
def contains_early_args (stx : Syntax) : CommandElabM Bool := do
  let decl := stx[1]
  if decl.getKind != ``Lean.Parser.Command.theorem then return false
  -- declSig consists of [binders, typeSpec]
  let binders := decl[2][0]
  return binders.getArgs.size > 0

-- Helper to check for answer(sorry) ↔ ...
def stars_with_answer_sorry_iff (stx : Syntax) : CommandElabM Bool := do
  let decl := stx[1]
  if decl.getKind != ``Lean.Parser.Command.theorem then return false
  -- declSig -> typeSpec [":", term]
  let typeSpec := decl[2][1]
  if typeSpec.getNumArgs < 2 then return false
  let term := typeSpec[1]

  -- Check kind against the identifier seen in your trace
  if term.getKind == `«term_↔_» then
    let lhs := term[0]
    return lhs.getKind == `Google.answer
  return false

/-- The actual linter object -/
def answerLinter : Linter where
  run := withSetOptionIn fun stx => do
    -- Ensure we are looking at a declaration
    if stx.getKind == ``Lean.Parser.Command.declaration then
      let answer_start ← stars_with_answer_sorry_iff stx
      let early_args ← contains_early_args stx

      if answer_start && early_args then
         logLintIf linter.style.answer_attribute stx
          "Move the quantifiers outward:
instead of
`theorem foo (bar : ℕ) (baz : ℕ) : answer(sorry) ↔ ...`
likely the intention was
`theorem foo : answer(sorry) ↔ ∀ᵉ (bar : ℕ) (baz : ℕ), ...`"
    return

initialize
  addLinter answerLinter

end AnswerLinter
