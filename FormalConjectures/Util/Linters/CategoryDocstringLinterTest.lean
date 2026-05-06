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

import FormalConjectures.Util.Linters.CategoryDocstringLinter

/-!
# Tests for the category docstring linter

This file contains test cases for the `CategoryDocstringLinter`, verifying that
research-open, research-solved, and textbook declarations without docstrings are flagged,
while declarations with docstrings or other categories are accepted.
-/

namespace CategoryDocstringLinter

/--
warning: Declarations tagged `@[category research open]`, `@[category research solved]`, or `@[category textbook]` must have a docstring.

Note: This linter can be disabled with `set_option linter.style.category_docstring false`
-/
#guard_msgs in
@[category research open]
theorem flagged_open_missing_docstring : True := by
  sorry

/--
warning: Declarations tagged `@[category research open]`, `@[category research solved]`, or `@[category textbook]` must have a docstring.

Note: This linter can be disabled with `set_option linter.style.category_docstring false`
-/
#guard_msgs in
@[category research solved]
theorem flagged_solved_missing_docstring : True := by
  trivial

#guard_msgs in
/-- A documented open problem statement should not be flagged. -/
@[category research open]
theorem not_flagged_with_docstring : True := by
  sorry

#guard_msgs in
@[category test]
theorem not_flagged_test_without_docstring : True := by
  trivial

/--
warning: Declarations tagged `@[category research open]`, `@[category research solved]`, or `@[category textbook]` must have a docstring.

Note: This linter can be disabled with `set_option linter.style.category_docstring false`
-/
#guard_msgs in
@[category textbook]
theorem flagged_textbook_missing_docstring : True := by
  trivial

end CategoryDocstringLinter
