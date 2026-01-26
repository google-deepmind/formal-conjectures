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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 82

Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$?

It is known that there must be at least $\Omega(\log n / \log \log n)$ zeros.

*Reference:*
- [Gr24] [Ben Green's Open Problem 82](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.82)
-/

open Real Set
open scoped Finset

namespace Green82

/--
Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$?
-/
@[category research open, AMS 11 42]
theorem green_82 :
    answer(sorry) ↔ ∃ f : ℕ → ℕ, ∀ n > 0, ∀ A : Finset ℤ, A.card = n →
      f n ≤ ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard := by
  sorry

/-- There must be at least $\Omega(\log n / \log \log n)$ zeros. -/
@[category research solved, AMS 11 42]
theorem green_82_lower_bound :
    ∃ c > 0, ∀ n ≥ 2, ∀ A : Finset ℤ, A.card = n →
      c * log n / log (log n) ≤
        ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard := by
  sorry

end Green82
