/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 936

*Reference:* [erdosproblems.com/936](https://www.erdosproblems.com/936)
-/
open Filter Nat

/--
The predicate that `a n` is only powerful for finitely many `n`.
-/
def EventuallyNotPowerful (a : ℕ → ℕ) : Prop := atTop.Eventually (fun n => ¬ (a n).Powerful)

/-- Is $2^n + 1$ powerful for finitely many $n$? -/
@[category research open, AMS 11]
theorem erdos_936.variants.two_pow_add_one :
   EventuallyNotPowerful (2 ^ · + 1) ↔ answer(sorry) := by
  sorry

/-- Is $2^n - 1$ powerful for finitely many $n$? -/
@[category research open, AMS 11]
theorem erdos_936.variants.two_pow_sub_one :
   EventuallyNotPowerful (2 ^ · - 1) ↔ answer(sorry) := by
  sorry

/-- Is $n! + 1$ powerful for finitely many $n$? -/
@[category research open, AMS 11]
theorem erdos_936.variants.factorial_add_one :
   EventuallyNotPowerful (·! + 1) ↔ answer(sorry) := by
  sorry

/-- Is $n! - 1$ powerful for finitely many $n$? -/
@[category research open, AMS 11]
theorem erdos_936.variants.factorial_sub_one :
   EventuallyNotPowerful (·! - 1) ↔ answer(sorry) := by
  sorry
