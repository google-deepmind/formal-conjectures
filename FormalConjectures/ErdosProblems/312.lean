# Copyright 2025 The Formal Conjectures Authors.

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     https://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 312

*Reference:* https://www.erdosproblems.com/312

We state a version of the problem using `Fin n → ℕ` families and `Finset (Fin n)` subsets
instead of multisets. This makes multiplicities explicit by indexing the family with `Fin n`.
-/

open scoped BigOperators Topology Real
open Filter

namespace Erdos312
noncomputable section

/--
`hsumIdx a S` is the harmonic sum of the entries of the indexed family `a : Fin n → ℕ`
restricted to a subset of indices `S : Finset (Fin n)`.
-/
def hsumIdx {n : ℕ} (a : Fin n → ℕ) (S : Finset (Fin n)) : ℝ :=
  ∑ i in S, (a i : ℝ)⁻¹

/--
`hsumAll a` is the total harmonic sum of all entries of `a : Fin n → ℕ`.
This is just the sum over all indices `Fin n`.
-/
def hsumAll {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ)⁻¹

@[simp]
lemma hsumIdx_empty {n} (a : Fin n → ℕ) : hsumIdx a ∅ = 0 := by
  simp [hsumIdx]

@[simp]
lemma hsumAll_eq_univ_sum {n} (a : Fin n → ℕ) :
  hsumAll a = ∑ i in (Finset.univ : Finset (Fin n)), (a i : ℝ)⁻¹ := by
  classical
  simp [hsumAll]

/-!
### Main theorem (fintype version)

The problem asks: does there exist a constant `c > 0` such that for every `K > 1`,
whenever `a : Fin n → ℕ` is large enough and has harmonic sum `> K`,
we can choose a subfamily (given by `S : Finset (Fin n)`) whose harmonic sum lies
in the interval `(1 - exp(-c*K), 1)`?
-/

/--
Fintype-indexed version of Erdős Problem 312.

- `c` is a positive universal constant.
- For each `K > 1`, there exists an `N₀` such that:
  - For all sufficiently large `n ≥ N₀` and families `a : Fin n → ℕ`,
  - If the total harmonic sum `hsumAll a > K`,
  - Then there exists a subset of indices `S : Finset (Fin n)` with
    `1 - exp(-(c*K)) < hsumIdx a S ≤ 1`.

This statement mirrors the original problem, but is easier to handle formally
because it avoids the subtlety of multiset-subset with multiplicities.
-/
@[category research open, AMS 5 11]
theorem erdos_312_fintype :
  (∃ᵉ (c : ℝ), 0 < c ∧
    ∀ (K : ℝ), 1 < K →
      ∃ (N₀ : ℕ),
        ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ hsumAll a > K) →
            ∃ (S : Finset (Fin n)),
              1 - Real.exp (-(c * K)) < hsumIdx a S ∧
              hsumIdx a S ≤ 1)
  ↔ answer (sorry) := by
  sorry

end Erdos312
