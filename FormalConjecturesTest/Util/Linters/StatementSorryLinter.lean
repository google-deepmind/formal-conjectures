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

public meta import FormalConjecturesUtil.Linters.StatementSorryLinter
public import FormalConjecturesUtil.Attributes.Basic

@[expose] public section

-- Off by default; on here because this file is what tests it.
set_option linter.style.statement_sorry true

namespace StatementSorryLinter

-- The unknown of a value question is the one allowed placeholder.
def a_value_question.answer : Nat := sorry

#guard_msgs in
@[category research open, question value, AMS 11]
theorem a_value_question : 2 + 2 = a_value_question.answer := by
  sorry

-- A definition built from an unknown is fine too: the `sorry` comes from the unknown.
def twice_the_answer : Nat := 2 * a_value_question.answer

#guard_msgs in
@[category test, AMS 11]
theorem about_twice_the_answer : twice_the_answer = 2 * a_value_question.answer := by
  rfl

-- A placeholder definition is not.
def a_placeholder : Nat := sorry

/--
warning: The statement depends on `sorry` through `StatementSorryLinter.a_placeholder`. Only the `answer` definition of a value question may be left as `sorry`.

Note: This linter can be disabled with `set_option linter.style.statement_sorry false`
-/
#guard_msgs in
@[category research open, AMS 11]
theorem uses_a_placeholder : a_placeholder = 4 := by
  sorry

-- Nor is a definition that uses a theorem proved by `sorry`.
theorem exists_witness : ∃ n : Nat, 2 < n := by
  sorry

noncomputable def a_witness : Nat := Classical.choose exists_witness

/--
warning: The statement depends on `sorry` through `StatementSorryLinter.a_witness`. Only the `answer` definition of a value question may be left as `sorry`.

Note: This linter can be disabled with `set_option linter.style.statement_sorry false`
-/
#guard_msgs in
@[category research open, AMS 11]
theorem uses_a_witness : 2 < a_witness := by
  sorry

-- Nor is a `sorry` in the statement itself.
/--
warning: The statement contains `sorry`. Only the `answer` definition of a value question may be left as `sorry`.

Note: This linter can be disabled with `set_option linter.style.statement_sorry false`
-/
#guard_msgs in
@[category research open, AMS 11]
theorem sorry_in_statement : (sorry : Nat) = 4 := by
  sorry

-- A statement whose proof is `sorry` is what this repository is made of.
#guard_msgs in
@[category research open, AMS 11]
theorem proof_is_sorry : 2 + 2 = 4 := by
  sorry

end StatementSorryLinter
