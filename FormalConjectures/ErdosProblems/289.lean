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
# Erdős Problem 289
*Reference:* [erdosproblems.com/289](https://www.erdosproblems.com/289)
-/

open Asymptotics Filter Finset

/-- Is it true that, for all sufficiently large $k$, there exists finite intervals
$I_1, \dotsc, I_k \subset \mathbb{N}$ with $|I_i| \geq 2$ for $1 \leq i \leq k$ such that
$$
1 = \sum_{i=1}^k \sum_{n \in I_i} \frac{1}{n}.
$$
-/
@[category research open, AMS 11]
theorem erdos_289 :
    (∀ᶠ k : ℕ in atTop, ∃ I : Fin k → Finset ℕ,
      (∀ i, 2 ≤ #(I i) ∧ ∃ a b, 0 < a ∧ I i = Finset.Icc a b) ∧
      ∑ i, ∑ n ∈ I i, (n⁻¹ : ℚ) = 1) ↔ answer(sorry) := by
  sorry
