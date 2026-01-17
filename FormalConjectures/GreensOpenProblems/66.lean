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
# Ben Green's Open Problem 66

*Reference:* [Ben Green's Open Problem 66](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 66)
-/

open Real

namespace Green66

/-- A natural number is a sum of two squares. -/
def IsSumTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/--
Is there always a sum of two squares between $X - \frac{1}{10} X^{1/4}$ and $X$?

This is a question about the gaps between sums of two squares, asking whether the gaps
are always at most $\frac{1}{10} X^{1/4}$ near $X$.
-/
@[category research open, AMS 11]
theorem green_66 :
    answer(sorry) ↔ ∀ X : ℕ, X > 0 →
      ∃ n : ℕ, IsSumTwoSquares n ∧ (X : ℝ) - (1/10) * X ^ (1/4 : ℝ) ≤ n ∧ n ≤ X := by
  sorry

end Green66
