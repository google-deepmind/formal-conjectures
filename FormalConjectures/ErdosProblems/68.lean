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

import FormalConjecturesUtil

/-!
# Erdős Problem 68

*Reference:* [erdosproblems.com/68](https://www.erdosproblems.com/68)
-/

namespace Erdos68

/--
Is
$$\sum_{n=2}^\infty \frac{1}{n!-1}$$
irrational?
-/
@[category research open, AMS 11]
theorem erdos_68 :
    answer(sorry) ↔ Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) := by
  sorry

/--
For the exact rational prefix $H_m = \sum_{k=2}^{m} 1/(k!-1)$, let
$Z_m = \lfloor m!\,H_m \rfloor + 1$ be its strict factorial-grid successor.
The series in `erdos_68` is irrational exactly when, beyond every cutoff, some
$Z_m$ fails to be divisible by its index $m$.

The right-hand side is a purely integral, exactly computable condition: no
real-number reasoning is needed to evaluate it at any index. The equivalence
is hypothesis-free.

This is an exact arithmetic reformulation of `erdos_68`; it does not decide
either side, and in particular does not establish that such divisibility
failures occur cofinally.
-/
@[category research solved, AMS 11, formal_proof using lean4 at
  "https://github.com/wcook04/plectis-lean-erdos249-257/blob/ceaee37f2df872af9e19c90f2b88d87f06fec85d/adapters/FormalConjecturesVariants.lean#L487-L494"]
theorem erdos_68.variants.iff_cofinal_divisibility_miss :
    Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ)) ↔
      ∀ B : ℕ, ∃ m : ℕ,
        B < m ∧
          ¬ ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) := by
  sorry

/--
$$\sum_{n=2}^\infty \frac{1}{n!-1} = \sum_{n=2}^\infty \sum_{k=1}^\infty \frac{1}{(n!)^k}$$
-/
@[category textbook, AMS 11]
theorem sum_factorial_inv_eq_geometric :
    let f (n k : ℕ) : ℝ := 1 / ((n + 2).factorial : ℝ) ^ (k + 1)
    ∑' n : ℕ, (1 : ℝ) / ((n + 2).factorial - 1) = ∑' n : ℕ, ∑' k : ℕ, f n k := by
  intro f
  apply tsum_congr
  intro n
  symm
  -- The inner sum is a geometric series with ratio r = ((n + 2)!)⁻¹.
  set r : ℝ := ((n + 2).factorial : ℝ)⁻¹ with hr_def
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_lt_one : r < 1 := inv_lt_one_of_one_lt₀ (by simp)
  -- Geometric series: HasSum (fun k ↦ r ^ k) ((1 - r)⁻¹)
  have hgeom := hasSum_geometric_of_lt_one hr_nonneg hr_lt_one
  -- Multiply by r to shift the index: HasSum (fun k ↦ r * r ^ k) (r * (1 - r)⁻¹)
  have hshift := hgeom.mul_left r
  -- Each summand satisfies f n k = r * r ^ k.
  have hf_eq : ∀ k, f n k = r * r ^ k := fun k => by simp only [f, hr_def]; ring
  -- Evaluate ∑' k, f n k = r * (1 - r)⁻¹ = 1 / ((n + 2)! - 1).
  exact ((hshift.congr_fun hf_eq).tsum_eq.trans (by simp only [hr_def]; field_simp))

end Erdos68
