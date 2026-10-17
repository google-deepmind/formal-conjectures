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

public meta import FormalConjecturesUtil.Linters.QuestionLinter

@[expose] public section

-- Off by default; on here because this file is what tests it.
set_option linter.style.question_attribute true

namespace QuestionLinter

def untagged_value_question.answer : Nat := sorry

/--
warning: The statement refers to its unknown `QuestionLinter.untagged_value_question.answer`, so it asks for a value; tag the theorem `@[question value]`.

Note: This linter can be disabled with `set_option linter.style.question_attribute false`
-/
#guard_msgs in
@[category research open, AMS 11]
theorem untagged_value_question : 2 + 2 = untagged_value_question.answer := by
  sorry

def tagged_value_question.answer : Nat := sorry

#guard_msgs in
@[category research open, question value, AMS 11]
theorem tagged_value_question : 2 + 2 = tagged_value_question.answer := by
  sorry

-- A `test` or `API` statement about another theorem's unknown is fine.
#guard_msgs in
@[category test, AMS 11]
theorem about_another_answer : tagged_value_question.answer = tagged_value_question.answer := by
  rfl

-- A research statement must not mention another theorem's unknown.
/--
warning: The statement refers to `QuestionLinter.tagged_value_question.answer`, the unknown of another question. A statement about its own unknown refers to `QuestionLinter.foreign_answer.answer`; a statement about `QuestionLinter.tagged_value_question.answer` belongs to a `test` or `API` theorem.

Note: This linter can be disabled with `set_option linter.style.question_attribute false`
-/
#guard_msgs in
@[category research open, AMS 11]
theorem foreign_answer : 2 + 2 = tagged_value_question.answer := by
  sorry

def foreign_answer_in_question.answer : Nat := sorry

/--
warning: The statement refers to `QuestionLinter.tagged_value_question.answer`, the unknown of another question. A statement about its own unknown refers to `QuestionLinter.foreign_answer_in_question.answer`; a statement about `QuestionLinter.tagged_value_question.answer` belongs to a `test` or `API` theorem.

Note: This linter can be disabled with `set_option linter.style.question_attribute false`
-/
#guard_msgs in
@[category research open, question value, AMS 11]
theorem foreign_answer_in_question :
    foreign_answer_in_question.answer = tagged_value_question.answer := by
  sorry

-- A yes-or-no question has no unknown and needs no `value`.
#guard_msgs in
@[category research open, question, AMS 11]
theorem a_yes_no_question : 2 + 2 = 4 := by
  sorry

-- The converse is checked by the attribute itself: `question value` without a reference to the
-- unknown is an error, whether or not a definition `answer` exists.
/--
error: `question value` requires the statement of 'QuestionLinter.tagged_without_answer' to refer to the definition `QuestionLinter.tagged_without_answer.answer`; for a yes-or-no question use `question`
-/
#guard_msgs in
@[category research open, question value, AMS 11]
theorem tagged_without_answer : 2 + 2 = 4 := by
  sorry

-- A filled-in answer still counts: the check is on the reference, not on `sorry`.
def filled_value_question.answer : Nat := 4

#guard_msgs in
@[category research solved, question value, AMS 11]
theorem filled_value_question : 2 + 2 = filled_value_question.answer := by
  rfl

end QuestionLinter
