import WeilPairedHadamardFixedLineV1
import Lc.LiCriterion.HadamardSummabilityBridge
import Lc.LiCriterion.XiGrowth
import Hadamard.OrderOne.LogDeriv
import Mathlib.Tactic

/-!
AEGIS Ω — paired Hadamard single-tsum fusion v1.

This module closes only the summability/fusion step left open by
`WeilPairedHadamardFixedLineV1`: each multiplicity-weighted genus-one
log-derivative family is summable away from the zero set, and the difference
of the two absolutely summable families may therefore be fused into the single
paired partial-fraction `tsum`.

No transport to the AEGIS zeta-zero carrier, Mellin evaluation, whole explicit
formula, sign inequality, global Weil positivity, or RH theorem is asserted.
-/

open Complex Filter
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- Multiplicity-weighted genus-one Hadamard terms are absolutely summable at
any evaluation point away from the completed-zeta zero set.  The proof mirrors
the provider's unweighted log-derivative majorant, now using the provider's
multiplicity-weighted inverse-square summability. -/
theorem riemannXi_weighted_hadamard_term_summable_v1
    (x : ℂ) (hx : ∀ ρ : LiCriterion.NontrivialZero, x ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (x / (ρ.val * (x - ρ.val)))) := by
  have hweighted :=
    LiCriterion.xi_weighted_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  have hunweighted :=
    LiCriterion.xi_genus_one_of_hadamard_order_one
      LiCriterion.XiGrowth.riemannXi_hasFiniteOrder
      LiCriterion.XiGrowth.riemannXi_order_le_one
  by_cases hx0 : x = 0
  · subst x
    simpa using
      (summable_zero : Summable (fun _ : LiCriterion.NontrivialZero => (0 : ℂ)))
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let g : LiCriterion.NontrivialZero → ℝ := fun ρ =>
    (2 * ‖x‖) *
      ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
  have hg : Summable g := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm] using
      hweighted.mul_left (2 * ‖x‖)
  refine Summable.of_norm_bounded_eventually
    (f := fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (x / (ρ.val * (x - ρ.val))))
    (g := g) hg ?_
  let S : Set LiCriterion.NontrivialZero :=
    {ρ | ‖ρ.val‖ ≤ (2 : ℝ) * ‖x‖}
  have hSfinite : S.Finite :=
    Hadamard.OrderOne.finite_norm_le_of_summable_inv_norm_sq
      (z := fun ρ : LiCriterion.NontrivialZero => ρ.val)
      (fun ρ => ρ.ne_zero) hunweighted
      (R := (2 : ℝ) * ‖x‖) (by nlinarith [hx_norm_pos])
  have hnotS : ∀ᶠ ρ in (cofinite : Filter LiCriterion.NontrivialZero), ρ ∉ S := by
    have : (Sᶜ : Set LiCriterion.NontrivialZero) ∈
        (cofinite : Filter LiCriterion.NontrivialZero) := by
      exact Filter.mem_cofinite.2 (by simpa using hSfinite)
    simpa using this
  filter_upwards [hnotS] with ρ hρ
  have hz_gt : (2 : ℝ) * ‖x‖ < ‖ρ.val‖ := by
    have : ¬ ‖ρ.val‖ ≤ (2 : ℝ) * ‖x‖ := by simpa [S] using hρ
    exact lt_of_not_ge this
  have hz_pos : 0 < ‖ρ.val‖ := norm_pos_iff.mpr ρ.ne_zero
  have hdist_pos : 0 < ‖x - ρ.val‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hx ρ))
  have hdist_lower : (1 / 2 : ℝ) * ‖ρ.val‖ ≤ ‖x - ρ.val‖ := by
    have hx_lt : ‖x‖ < (1 / 2 : ℝ) * ‖ρ.val‖ := by linarith [hz_gt]
    have hsub_lt : (1 / 2 : ℝ) * ‖ρ.val‖ < ‖ρ.val‖ - ‖x‖ := by
      linarith [hx_lt]
    have hsub_le : ‖ρ.val‖ - ‖x‖ ≤ ‖x - ρ.val‖ := by
      have h := norm_sub_norm_le ρ.val x
      simpa [norm_sub_rev] using h
    exact le_trans (le_of_lt hsub_lt) hsub_le
  have hhalf_pos : 0 < (1 / 2 : ℝ) * ‖ρ.val‖ ^ 2 := by positivity
  have hden_le :
      (1 / 2 : ℝ) * ‖ρ.val‖ ^ 2 ≤ ‖ρ.val‖ * ‖x - ρ.val‖ := by
    have h := mul_le_mul_of_nonneg_left hdist_lower (le_of_lt hz_pos)
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h
  have hinv_le :
      (1 : ℝ) / (‖ρ.val‖ * ‖x - ρ.val‖) ≤
        (2 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    have h' :
        (1 : ℝ) / (‖ρ.val‖ * ‖x - ρ.val‖) ≤
          (1 : ℝ) / ((1 / 2 : ℝ) * ‖ρ.val‖ ^ 2) :=
      one_div_le_one_div_of_le hhalf_pos hden_le
    have heq :
        (1 : ℝ) / ((1 / 2 : ℝ) * ‖ρ.val‖ ^ 2) =
          (2 : ℝ) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
      field_simp
    exact h'.trans_eq heq
  have hnorm :
      ‖x / (ρ.val * (x - ρ.val))‖ ≤
        (2 * ‖x‖) * ((1 : ℝ) / ‖ρ.val‖ ^ 2) := by
    have heq :
        ‖x / (ρ.val * (x - ρ.val))‖ =
          ‖x‖ * ((1 : ℝ) / (‖ρ.val‖ * ‖x - ρ.val‖)) := by
      simp [div_eq_mul_inv, mul_comm]
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_left hinv_le (norm_nonneg x)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hm_nonneg :
      0 ≤ (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) := by positivity
  calc
    ‖(analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (x / (ρ.val * (x - ρ.val)))‖ =
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
          ‖x / (ρ.val * (x - ρ.val))‖ := by simp
    _ ≤ (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
          ((2 * ‖x‖) * ((1 : ℝ) / ‖ρ.val‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hnorm hm_nonneg
    _ = g ρ := by
      simp [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The already pointwise-paired partial-fraction kernel is summable with the
same analytic multiplicities. -/
theorem riemannXi_paired_kernel_summable_v1
    (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    Summable (fun ρ : LiCriterion.NontrivialZero =>
      (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
        (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val)))) := by
  have ha := riemannXi_weighted_hadamard_term_summable_v1 s hs
  have hb := riemannXi_weighted_hadamard_term_summable_v1 (1 - s) h1s
  have hsub := ha.sub hb
  have hfun :
      (fun ρ : LiCriterion.NontrivialZero =>
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            (s / (ρ.val * (s - ρ.val))) -
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            ((1 - s) / (ρ.val * ((1 - s) - ρ.val)))) =
      (fun ρ : LiCriterion.NontrivialZero =>
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val)))) := by
    funext ρ
    rw [← mul_sub]
    congr 1
    exact paired_hadamard_partial_fraction_v1
      s ρ.val ρ.ne_zero (hs ρ) (h1s ρ)
  rw [hfun] at hsub
  exact hsub

/-- The difference-of-two-tsums theorem from #519 is exactly one absolutely
summable paired partial-fraction `tsum`. -/
theorem riemannXi_paired_hadamard_tsum_v1
    (s : ℂ)
    (hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val)
    (h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val) :
    2 * _root_.logDeriv LiCriterion.riemannXi s =
      ∑' ρ : LiCriterion.NontrivialZero,
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val))) := by
  rw [riemannXi_paired_hadamard_difference_v1 s hs h1s]
  have ha := riemannXi_weighted_hadamard_term_summable_v1 s hs
  have hb := riemannXi_weighted_hadamard_term_summable_v1 (1 - s) h1s
  rw [← ha.tsum_sub hb]
  apply tsum_congr
  intro ρ
  rw [← mul_sub]
  congr 1
  exact paired_hadamard_partial_fraction_v1
    s ρ.val ρ.ne_zero (hs ρ) (h1s ρ)

end

#print axioms riemannXi_weighted_hadamard_term_summable_v1
#print axioms riemannXi_paired_kernel_summable_v1
#print axioms riemannXi_paired_hadamard_tsum_v1
