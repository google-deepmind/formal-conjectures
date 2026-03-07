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

import FormalConjectures.Util.Linters.ExistsImplicationLinter
import Mathlib

/--
warning: Declaration contains the pattern the expression ∃ n, n ≠ 0 → False. Did you mean ∃ n, n ≠ 0 ∧ False?

Note: This linter can be disabled with `set_option linter.style.existsImplication false`
-/
#guard_msgs in
theorem this_doesnt_look_good : ∃ n : Nat, n ≠ 0 → False := by
  use 0
  trivial

/--
warning: Declaration contains the pattern the expression ∃ n, n ≠ 0 → n ≠ 1 → False. Did you mean ∃ n, n ≠ 0 ∧ n ≠ 1 ∧ False?

Note: This linter can be disabled with `set_option linter.style.existsImplication false`
-/
#guard_msgs in
theorem even_worse : ∃ n : Nat, n ≠ 0 → n ≠ 1 → False := by
  use 0
  trivial

#guard_msgs in
theorem this_is_fine : ∃ n : Nat, n ≠ 0 ∨ False := by
  sorry
