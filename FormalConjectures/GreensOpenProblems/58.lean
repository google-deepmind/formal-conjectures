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

open scoped Pointwise

/-!
# Ben Green's Open Problem 58

*Reference:* [Ben Green's Open Problem 58](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 58)
-/

namespace Green58

/- The analytic lower bound on the size of the sets in the conjecture. Here `((49 : ℝ) / 100)` is
`0.49`. -/

/--
Suppose $A, B ⊆ \{1, \dots, N\}$ both have size at least $N^{0.49}$. Must the sumset $A + B$
contain a composite number?
-/
@[category research open, AMS 5 11]
theorem green_58 :
    answer(sorry) ↔
      ∀ᵉ (N ≥ (1 : ℕ)) (A ⊆ Finset.Icc 1 N) (B ⊆ Finset.Icc 1 N),
        (N : ℝ) ^ (0.49 : ℝ) ≤ (A.card : ℝ) →
        (N : ℝ) ^ (0.49 : ℝ) ≤ (B.card : ℝ) →
        ∃ m ∈ (A + B), m.Composite := by
  sorry

end Green58
