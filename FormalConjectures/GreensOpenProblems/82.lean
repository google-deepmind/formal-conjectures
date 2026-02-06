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

It is known that there are sets $A$ for which the number of zeros is at most $C(n \log n)^{2/3}$
(Juškevičius & Sahasrabudhe, 2020). For sufficiently large $n$, every set $A$ has at least
$(\log \log n)^c$ zeros (Bedert, 2025).

*References:*
- [Ben Green's Open Problem 82](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.82)
- [An improved lower bound for a problem of Littlewood on the zeros of cosine polynomials](https://arxiv.org/abs/2407.16075) (Bedert, 2025)
- [Cosine polynomials with few zeros](https://arxiv.org/abs/2005.01695) (Juškevičius & Sahasrabudhe, 2020)
-/

open Real Set
open scoped Finset

namespace Green82

/-- The minimum number of zeros in $[0,1)$ of $\sum_{a \in A} \cos(2\pi a\theta)$
over all sets $A \subset \mathbb{Z}$ of size $n$. -/
noncomputable def minZeros (n : ℕ) : ℕ∞ :=
  ⨅ A : {A : Finset ℤ // A.card = n},
    ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A.val, cos (2 * π * a * θ) = 0} : Set ℝ).ncard

/-- Let $A \subset \mathbb{Z}$ be a set of size $n$. For how many $\theta \in \mathbb{R}/\mathbb{Z}$
must we have $\sum_{a \in A} \cos(2\pi a\theta) = 0$? The answer is `minZeros n`. -/
@[category research open, AMS 11 42]
theorem green_82 : ∀ n ≥ 1, answer(sorry) = minZeros n := by
  sorry

/-- Lower bound: every set has at least $(\log \log n)^c$ zeros. -/
@[category research solved, AMS 11 42]
theorem green_82_lower_bound :
    ∃ c > 0, ∃ n₀, ∀ n ≥ n₀, ∀ A : Finset ℤ, A.card = n →
      (⌊Real.log (Real.log n) ^ c⌋₊ : ℕ∞) ≤
      ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard := by
  sorry

/-- Upper bound: there exists $A$ with at most $C(n \log n)^{2/3}$ zeros. -/
@[category research solved, AMS 11 42]
theorem green_82_upper_bound :
    ∃ C > 0, ∀ n ≥ 1, ∃ A : Finset ℤ, A.card = n ∧
      ({θ : ℝ | θ ∈ Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard ≤
      (⌊C * (n * Real.log n) ^ (2 / 3 : ℝ)⌋₊ : ℕ∞) := by
  sorry

end Green82
