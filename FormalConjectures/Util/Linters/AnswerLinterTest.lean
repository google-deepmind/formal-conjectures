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

import FormalConjectures.Util.Linters.AnswerLinter
import FormalConjectures.Util.Answer

/-!
# Tests for the answer linter

This file contains test cases for the `AnswerLinter`, verifying that it correctly flags
theorems with early arguments when `answer(sorry)` is the left-hand side of an iff,
and does not flag theorems without `answer(sorry)` or without early arguments.
-/

namespace AnswerLinter

/--
warning: Move the quantifiers outward:
instead of
`theorem foo (bar : ℕ) (baz : ℕ) : answer(sorry) ↔ ...`
likely the intention was
`theorem foo : answer(sorry) ↔ ∀ᵉ (bar : ℕ) (baz : ℕ), ...`

Note: This linter can be disabled with `set_option linter.style.answer_attribute false`
-/
#guard_msgs in
/-- An exampe of what we want to lint against -/
theorem flagged_by_linter (h : True) (b : Nat) : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry

#guard_msgs in
/-- An non-exampe: we want don't to lint against this case -/
theorem not_flagged_no_answer_sorry (_ : True) (_ : Nat) : 1 + 1 = 2 := by
  rfl

#guard_msgs in
/-- An non-exampe: we want don't to lint against this case-/
theorem not_flagged_no_arguments : answer(sorry) ↔ 1 + 1 = 2 := by
  sorry

#guard_msgs in
/-- An non-exampe: here `answer(sorry)` is not a `Prop`, and not the entire left
hand side of the iff. -/
theorem not_flagged_non_prop_answer (h : True) (b : Nat) : answer(sorry) = 2 ↔ 1 + 1 = 2 := by
  sorry


end AnswerLinter
