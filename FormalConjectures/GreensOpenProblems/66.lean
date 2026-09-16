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

import FormalConjecturesUtil

/-!
# Ben Green's Open Problem 66

*Reference:* [Ben Green's Open Problem 66](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8)
-/

open Filter

namespace Green66

/-- A natural number is a sum of two squares if it can be written as `a ^ 2 + b ^ 2`. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/--
Is there always a sum of two squares between $X - \frac{1}{10}X^{1/4}$ and $X$?
We formalize this as an eventual statement for sufficiently large real $X$.
-/
@[category research open, AMS 11]
theorem green_66 :
    answer(sorry) ↔
      ∀ᶠ X : ℝ in atTop,
        ∃ n : ℕ, IsSumOfTwoSquares n ∧
          (n : ℝ) ∈ Set.Icc (X - (1 / 10 : ℝ) * X ^ (1 / 4 : ℝ)) X := by
  sorry

/--
Green notes that a well-known, almost trivial argument gives an $O(X^{1/4})$ bound on the left.
-/
@[category research solved, AMS 11]
theorem green_66.variants.trivial_bound :
    ∃ C > (0 : ℝ), ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, IsSumOfTwoSquares n ∧
        (n : ℝ) ∈ Set.Icc (X - C * X ^ (1 / 4 : ℝ)) X := by
  -- Subtract the greatest square `u ^ 2` below `X`, then the greatest square `v ^ 2`
  -- below `X - u ^ 2`.
  sorry

end Green66
