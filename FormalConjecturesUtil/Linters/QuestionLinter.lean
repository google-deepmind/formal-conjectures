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
module

public import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesUtil.Linters.Util
public import Mathlib.Tactic.Lemma

/-! # The Question Linter

The `QuestionLinter` checks two things about the unknown `<theorem>.answer` of a value question:

- The `question` attribute is not forgotten: a theorem whose statement refers to its own
  unknown must carry `@[question value]`. The attribute itself checks the converse, that a
  tagged theorem does refer to its unknown.
- A research statement mentions no other theorem's unknown: a statement that refers to
  `bar.answer` from `theorem foo` is most likely a copy-and-paste error. A `test` or `API`
  statement about an unknown is fine.
-/

public meta section

open Lean Elab Meta Linter Command Parser Term ProblemAttributes

register_option linter.style.question_attribute : Bool := {
  defValue := false
  descr := "enable the linter checking that a value question carries `question value`"
}

namespace QuestionLinter

/-- Warns when the statement of the theorem `declName` refers to `declName.answer` but the
theorem is not tagged `@[question value]`. -/
def checkValueQuestionTagged (declName : Name) (declId : Syntax) : CommandElabM Unit := do
  let some info := (← getEnv).find? declName | return
  unless info.type.getUsedConstants.contains (declName ++ `answer) do return
  unless (← getQuestionKind? declName) == some .value do
    logLintIf linter.style.question_attribute declId
      m!"The statement refers to its unknown `{declName ++ `answer}`, so it asks for a value; \
        tag the theorem `@[question value]`."

/-- Warns when the statement of the research theorem `declName`, or of a theorem tagged
`question`, refers to the unknown `bar.answer` of another theorem. -/
def checkNoForeignAnswer (declName : Name) (declId : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | return
  let isResearch := (categoryExt.getState env).toArray.any fun t =>
    t.declName == declName && t.category matches .research _
  unless isResearch || (← getQuestionKind? declName).isSome do return
  for c in info.type.getUsedConstants do
    if c.getString! == "answer" && c != declName ++ `answer then
      logLintIf linter.style.question_attribute declId
        m!"The statement refers to `{c}`, the unknown of another question. A statement about \
          its own unknown refers to `{declName ++ `answer}`; a statement about `{c}` belongs \
          to a `test` or `API` theorem."

/-- The question linter checks that a theorem using its `answer` definition is tagged
`@[question value]`, and that a research statement uses no other theorem's `answer`. -/
def questionLinter : Linter where
  run := withSetOptionIn fun stx => do
    match stx with
    | `(command| $mods:declModifiers theorem $declId:declId $_:declSig $_:declVal)
    | `(command| $mods:declModifiers lemma $declId:declId $_:declSig $_:declVal) =>
      let declName ← FormalConjectures.Linter.resolveDeclName mods declId
      checkValueQuestionTagged declName declId
      checkNoForeignAnswer declName declId
    | _ => return

initialize do
  addLinter questionLinter

end QuestionLinter
