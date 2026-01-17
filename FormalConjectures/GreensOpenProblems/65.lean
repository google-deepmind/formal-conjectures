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
# Ben Green's Open Problem 65

*Reference:* [Ben Green's Open Problem 65](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#section.8 Problem 65)
-/

namespace Green65

/--
Is there $c > 0$ with the following property: whenever $A \subset [N]$ is a set of size $N^{1-c}$,
$A - A$ contains a nonzero square?
-/
@[category research open, AMS 5 11]
theorem green_65a :
    answer(sorry) ↔ ∃ c > (0 : ℝ),
      ∀ N : ℕ, ∀ (A : Finset ℕ),
        (∀ a ∈ A, a ∈ Finset.Icc 1 N) →
        (A.card : ℝ) ≥ N ^ (1 - c) →
          ∃ d ∈ A - A, d ≠ 0 ∧ IsSquare d := by
  sorry

/--
Is there $c > 0$ with the following property: whenever $A \subset [N]$ is a set of size $N^{1-c}$,
$A - A$ contains a prime minus one?
-/
@[category research open, AMS 5 11]
theorem green_65b :
    answer(sorry) ↔ ∃ c > (0 : ℝ),
      ∀ N : ℕ, ∀ (A : Finset ℕ),
        (∀ a ∈ A, a ∈ Finset.Icc 1 N) →
        (A.card : ℝ) ≥ N ^ (1 - c) →
          ∃ d ∈ A - A, ∃ p : ℕ, p.Prime ∧ d = p - 1 := by
  sorry

end Green65
