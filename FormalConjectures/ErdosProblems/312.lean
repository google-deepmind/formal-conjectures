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
# Erdős Problem 312 — Fintype Formulation

*Reference:* https://www.erdosproblems.com/312

We state a version of the problem using `Fin n → ℕ` families and `Finset (Fin n)` subsets
instead of multisets. This makes multiplicities explicit by indexing with `Fin n`.
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
  ∑ i ∈ S, (a i : ℝ)⁻¹

/--
`hsumAll a` is the total harmonic sum of all entries of `a : Fin n → ℕ`.
This is just the sum over all indices `Fin n`.
-/
def hsumAll {n : ℕ} (a : Fin n → ℕ) : ℝ :=
  ∑ i : Fin n, (a i : ℝ)⁻¹

@[simp]
lemma hsumIdx_empty {n} (a : Fin n → ℕ) : hsumIdx a ∅ = 0 := by
  simp [hsumIdx]

/--
`simp` lemma: `hsumIdx a` over `Finset.univ` coincides with `hsumAll a`.
-/
@[simp]
lemma hsumIdx_univ {n} (a : Fin n → ℕ) :
    hsumIdx a (Finset.univ : Finset (Fin n)) = hsumAll a := by
  simp [hsumIdx, hsumAll]

/--
`simp` lemma: `hsumAll a` is the same as summing over all indices of `Fin n`.
This is just the definition of `hsumAll` unfolded as a sum over `Finset.univ`.
-/
@[simp]
lemma hsumAll_eq_univ_sum {n} (a : Fin n → ℕ) :
    hsumAll a = ∑ i ∈ (Finset.univ : Finset (Fin n)), (a i : ℝ)⁻¹ := by
  -- no `classical` needed
  simp [hsumAll]

/-!
### Main theorem (fintype version)

Does there exist a constant `c > 0` such that for every `K > 1`, whenever the total
harmonic sum `∑ i, 1 / a i` exceeds `K` and `n` is large enough, we can choose a subset
of indices whose harmonic sum lies in `(1 - exp (-c*K), 1]`?
-/

/--
Fintype-indexed scaffold for Erdős Problem 312.

- `c` is a positive universal constant.
- For each `K > 1`, there exists `N₀` such that for all `n ≥ N₀` and families `a : Fin n → ℕ`
  with `hsumAll a > K`, there exists `S : Finset (Fin n)` satisfying
  `1 - exp (-(c*K)) < hsumIdx a S ≤ 1`.

This is a theorem skeleton; the proof is left as `sorry`.
-/
-- Note: if your CI forbids unknown attributes, remove any custom attributes like the one below.
-- @[category research open, AMS 5 11]
theorem erdos_312_fintype :
  ∃ (c : ℝ), 0 < c ∧
    ∀ (K : ℝ), 1 < K →
      ∃ (N₀ : ℕ),
        ∀ (n : ℕ) (a : Fin n → ℕ),
          (n ≥ N₀ ∧ hsumAll a > K) →
            ∃ (S : Finset (Fin n)),
              1 - Real.exp (-(c * K)) < hsumIdx a S ∧
              hsumIdx a S ≤ 1 := by
  /-
  Proof sketch (to be filled):
  1. Fix `K > 1`, let ε := exp (-c*K).
  2. Randomly thin indices with Bernoulli(p_i) where p_i := min (1, τ * a i).
  3. Tune τ so E[∑ X_i / a i] = 1 - ε/2; bound Var ≤ C/K using ∑ 1/(a i) > K.
  4. Apply Chebyshev/Hoeffding to get positive probability of (1 - ε, 1].
  5. Take the ω realizing it; its support defines `S`.
  -/
  sorry

end Erdos312
