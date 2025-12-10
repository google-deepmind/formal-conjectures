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
# Erdős Problem 1097

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

namespace Erdos1097

/--
Given a finite set of integers `A` (modelled as a `Finset ℤ`), the set
`CommonDifferencesThreeTermAP A` consists of all integers `d` such that there
is a non-trivial three-term arithmetic progression `a, b, c ∈ A` with
`b - a = d` and `c - b = d`.
-/
def CommonDifferencesThreeTermAP (A : Finset ℤ) : Set ℤ :=
  {d : ℤ | d ≠ 0 ∧ ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b - a = d ∧ c - b = d}

/--
The main conjecture: for any finite set of integers $A$ with $|A| = n$, the number of distinct
common differences in three-term arithmetic progressions is $O(n^{3/2})$.
-/
@[category research open, AMS 11]
theorem erdos_1097 : (∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
    (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (3 / 2 : ℝ)) ↔ answer(sorry) := by
  sorry

/--
A weaker bound has been proven: there are always $O(n^2)$ such values of $d$.
-/
@[category research solved, AMS 11]
theorem erdos_1097.variants.weaker : (∃ C > (0 : ℝ), ∀ (A : Finset ℤ),
    (CommonDifferencesThreeTermAP A).ncard ≤ C * (A.card : ℝ) ^ (2 : ℝ)) ↔ answer(sorry) := by
  sorry

/--
A trivial lower bound: there are always at least $Ω(n)$ such values of $d$ in the worst case.
-/
@[category research open, AMS 11]
theorem erdos_1097.variants.lower_bound : (∀ (n : ℕ), ∃ (A : Finset ℤ),
    A.card = n ∧ ∃ c > (0 : ℝ), c * (n : ℝ) ≤ (CommonDifferencesThreeTermAP A).ncard) ↔ answer(sorry) := by
  sorry

end Erdos1097
