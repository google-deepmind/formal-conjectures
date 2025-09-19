/-
Copyright 2025 The Formal Conjectures Authors

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

We state a version of the problem using functions `Fin n → ℕ` to represent a finite
indexed family of positive integers and `Finset (Fin n)` for chosen subsets,
making multiplicities explicit by indexing with `Fin n`.
-/

open scoped BigOperators
open Filter

namespace Erdos312

noncomputable section

variable {n : ℕ}

/-- A short name for a finite family of (nonnegative) integers indexed by `Fin n`. -/
abbrev Family (n : ℕ) := Fin n → ℕ

/-- Harmonic sum of the entries of `a` over the index set `S`. -/
def hsumIdx (a : Family n) (S : Finset (Fin n)) : ℝ :=
  ∑ i in S, (1 : ℝ) / (a i : ℝ)

/-- Total harmonic sum of all entries of the indexed family `a`. -/
def hsumAll (a : Family n) : ℝ :=
  ∑ i : Fin n, (1 : ℝ) / (a i : ℝ)

@[simp]
lemma hsumIdx_empty (a : Family n) : hsumIdx a ∅ = 0 := by
  simp [hsumIdx]

@[simp]
lemma hsumAll_univ (a : Family n) :
    hsumAll a = ∑ i in (Finset.univ : Finset (Fin n)), (1 : ℝ) / (a i : ℝ) := by
  classical
  simp [hsumAll]

/-!
## Main theorem (fintype version, scaffold)

Does there exist a constant `c > 0` such that for every `K > 1`, whenever the total
harmonic sum `∑ i, 1 / a i` exceeds `K` and `n` is large enough, we can choose a subset
of indices whose harmonic sum lies in `(1 - exp (-(c*K)), 1]`?
-/

/--
Fintype-indexed scaffold for Erdős Problem 312.

- `c` is a positive universal constant.
- For each `K > 1`, there exists `N₀` such that for all `n ≥ N₀` and families `a : Fin n → ℕ`
  with `hsumAll a > K`, there exists `S : Finset (Fin n)` satisfying
  `1 - Real.exp (-(c*K)) < hsumIdx a S ∧ hsumIdx a S ≤ 1`.

This is a theorem skeleton; the proof is left as `sorry`.
-/
@[category research open, AMS 5 11]
theorem erdos_312_fintype :
  ∃ (c : ℝ), 0 < c ∧
    ∀ (K : ℝ), 1 < K →
      ∃ (N₀ : ℕ),
        ∀ (n : ℕ) (a : Family n),
          (n ≥ N₀ ∧ hsumAll a > K) →
            ∃ (S : Finset (Fin n)),
              1 - Real.exp (-(c * K)) < hsumIdx a S ∧
              hsumIdx a S ≤ 1 := by
  /-
  Proof sketch (to be filled):
  1. Fix `K > 1`, let ε := Real.exp (-(c*K)).
  2. Randomly thin indices with Bernoulli(p_i) where p_i := min (1, τ * a i).
  3. Tune τ so E[∑ X_i / a i] = 1 - ε/2; bound Var ≤ C/K using ∑ 1/(a i) > K.
  4. Apply Chebyshev/Hoeffding to get positive probability of (1 - ε, 1].
  5. Take the ω realizing it; its support defines `S`.
  -/
  sorry

end  -- noncomputable section

end Erdos312
