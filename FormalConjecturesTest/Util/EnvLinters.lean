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

public meta import FormalConjecturesUtil.EnvLinters
public import Batteries.Tactic.Lint

@[expose] public section

namespace EnvLinters

-- Declarations the linters accept.

def a_value_question.answer : Nat := sorry

@[category research open, question value, AMS 11]
theorem a_value_question : 2 + 2 = a_value_question.answer := by
  sorry

@[category research open, question, AMS 11]
theorem a_yes_no_question : 2 + 2 = 4 := by
  sorry

@[category test, AMS 11]
theorem a_sanity_check : a_value_question.answer = a_value_question.answer := by
  rfl

-- Declarations the linters report.

@[category research open, AMS 11]
theorem open_but_proved : 2 + 2 = 4 := by
  rfl

def untagged_value_question.answer : Nat := sorry

@[category research open, AMS 11]
theorem untagged_value_question : 2 + 2 = untagged_value_question.answer := by
  sorry

@[category research open, AMS 11]
theorem about_another_answer : 2 + 2 = a_value_question.answer := by
  sorry

theorem exists_witness : ∃ n : Nat, 2 < n := by
  sorry

noncomputable def a_witness : Nat := Classical.choose exists_witness

@[category research open, AMS 11]
theorem uses_a_witness : 2 < a_witness := by
  sorry

/--
error: -- Found 4 errors in 11 declarations (plus 0 automatically generated ones) in the current file with 4 linters

/- The `foreignAnswer` linter reports:
STATEMENTS REFERRING TO ANOTHER THEOREM'S `answer`:
This linter can be disabled with `@[nolint foreignAnswer]`. -/
#check about_another_answer /- refers to `EnvLinters.a_value_question.answer`, the unknown of another question; a statement about its own unknown refers to `EnvLinters.about_another_answer.answer`, and a statement about `EnvLinters.a_value_question.answer` belongs to a `test` or `API` theorem -/

/- The `researchOpenSorryFree` linter reports:
`research open` PROBLEMS WITH A `sorry`-FREE PROOF:
This linter can be disabled with `@[nolint researchOpenSorryFree]`. -/
#check open_but_proved /- has a `sorry`-free proof, so it is not `research open` -/

/- The `statementSorry` linter reports:
STATEMENTS DEPENDING ON `sorry`:
This linter can be disabled with `@[nolint statementSorry]`. -/
#check uses_a_witness /- depends on `sorry` through `EnvLinters.a_witness`; only the `answer` definition of a value question may be left as `sorry` -/

/- The `valueQuestionTag` linter reports:
STATEMENTS ABOUT THEIR OWN `answer` WITHOUT `question value`:
This linter can be disabled with `@[nolint valueQuestionTag]`. -/
#check untagged_value_question /- refers to its unknown `EnvLinters.untagged_value_question.answer`, so it asks for a value; tag the theorem `@[question value]` -/
-/
#guard_msgs in
#lint only researchOpenSorryFree valueQuestionTag foreignAnswer statementSorry

end EnvLinters
