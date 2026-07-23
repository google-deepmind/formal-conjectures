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

import FormalConjecturesUtil.Linters.LatexDocstringLinter

/-!
# Tests for the LaTeX docstring linter

This file contains test cases for the `LatexDocstringLinter`, verifying that
docstrings with backslash-bracket or backslash-parenthesis are flagged.
-/

namespace LatexDocstringLinter


/--
warning: Docstrings should use `$ $` or `$$ $$` for math formulas instead of `\[ \]` or `\( \)`.

Note: This linter can be disabled with `set_option linter.style.latex_docstring false`
-/
#guard_msgs in
/-- This is a bad docstring with \[ math \]. -/
theorem flagged_with_bracket_math : True := by
  trivial

/--
warning: Docstrings should use `$ $` or `$$ $$` for math formulas instead of `\[ \]` or `\( \)`.

Note: This linter can be disabled with `set_option linter.style.latex_docstring false`
-/
#guard_msgs in
/-- This is a bad docstring with \( math \). -/
theorem flagged_with_paren_math : True := by
  trivial

#guard_msgs in
/-- This is a good docstring with $$ math $$. -/
theorem not_flagged_with_good_math : True := by
  trivial

end LatexDocstringLinter
