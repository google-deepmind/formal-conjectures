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

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Width quantifiers in finite Gram positivity

The quadratic form `sum z_i² - r * (sum z_i)²` is nonnegative in each
fixed finite dimension when `r` is sufficiently small.  No positive `r`
works in every dimension.  The dimension-dependent form is continuous.

This is a counterexample to interchanging `∀ n, ∃ r > 0` with
`∃ r > 0, ∀ n` in a Gram positivity argument.  It makes no assertion that
the analogous AEGIS finite-shift theorem is false.
-/

open scoped BigOperators

set_option autoImplicit false

namespace AEGIS.RHWidthQuantifierObstructionV1

/-- A diagonal quadratic form with one negative rank-one correction. -/
def gram (r : ℝ) (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  (∑ i, z i ^ 2) - r * (∑ i, z i) ^ 2

/-- The sharp positivity condition is `r * n ≤ 1`. -/
theorem gram_nonnegative_iff (r : ℝ) (n : ℕ) (hr : 0 ≤ r) :
    (∀ z : Fin n → ℝ, 0 ≤ gram r n z) ↔ r * (n : ℝ) ≤ 1 := by
  constructor
  · intro h
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hones := h (fun _ => 1)
      simp [gram] at hones
      nlinarith
  · intro h z
    have henergy : 0 ≤ ∑ i : Fin n, z i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (z i)
    have hcs : (∑ i : Fin n, z i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, z i ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := z))
    have hmul := mul_le_mul_of_nonneg_left hcs hr
    have hbound := mul_le_mul_of_nonneg_right h henergy
    unfold gram
    nlinarith

/-- Every fixed finite dimension admits a strictly positive width. -/
theorem every_finite_dimension_has_positive_width (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Fin n → ℝ, 0 ≤ gram r n z := by
  refine ⟨1 / ((n : ℝ) + 1), by positivity, ?_⟩
  apply (gram_nonnegative_iff _ n (by positivity)).mpr
  have hn : (0 : ℝ) ≤ n := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- Every fixed positive width has an explicit negative all-ones direction
in some sufficiently large finite dimension. -/
theorem every_positive_width_has_negative_dimension (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, gram r n (fun _ => 1) < 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / r)
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity : (0 : ℝ) < 1 / r) hn
  have hlarge : 1 < r * (n : ℝ) := by
    have h := (div_lt_iff₀ hr).mp hn
    nlinarith
  have hprod := mul_neg_of_pos_of_neg hnpos (sub_neg.mpr hlarge)
  refine ⟨n, ?_⟩
  simp only [gram, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  nlinarith

/-- Finite Gram forms are continuous despite the width-quantifier obstruction. -/
theorem gram_continuous (r : ℝ) (n : ℕ) :
    Continuous (gram r n) := by
  unfold gram
  fun_prop

/-- Finite-dimensional positivity at separately chosen widths does not give
a common positive width for all finite-dimensional spans. -/
theorem no_common_positive_width :
    ¬ ∃ r : ℝ, 0 < r ∧ ∀ (n : ℕ) (z : Fin n → ℝ), 0 ≤ gram r n z := by
  rintro ⟨r, hr, h⟩
  obtain ⟨n, hn⟩ := every_positive_width_has_negative_dimension r hr
  exact (not_lt_of_ge (h n (fun _ => 1))) hn

end AEGIS.RHWidthQuantifierObstructionV1

#print axioms AEGIS.RHWidthQuantifierObstructionV1.gram_nonnegative_iff
#print axioms AEGIS.RHWidthQuantifierObstructionV1.every_finite_dimension_has_positive_width
#print axioms AEGIS.RHWidthQuantifierObstructionV1.every_positive_width_has_negative_dimension
#print axioms AEGIS.RHWidthQuantifierObstructionV1.gram_continuous
#print axioms AEGIS.RHWidthQuantifierObstructionV1.no_common_positive_width
