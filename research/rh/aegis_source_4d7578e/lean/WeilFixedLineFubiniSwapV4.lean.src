import WeilMellinWeightedFixedLineV2
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
AEGIS Ω — fixed-line Fubini / paired-Hadamard assembly v4.

This module consumes the exact FZ absolute product-integral certificate from
WeilFixedLineFubiniCoreV3 and turns it into the actual integral-tsum exchange.
It then composes that exchange with the already kernel-verified paired
Hadamard kernel identity.

No gamma/digamma evaluation, whole explicit-formula identity, arithmetic sign,
global Weil positivity, or RH conclusion is asserted here.
-/

open Complex MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false

noncomputable section

private theorem fubini_fixed_line_left_ne_v4
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ((c : ℂ) + (t : ℂ) * I) ≠ ρ.val := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith [ρ.property.2.2]

private theorem fubini_one_sub_fixed_line_ne_v4
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    1 - ((c : ℂ) + (t : ℂ) * I) ≠ ρ.val := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith [ρ.property.2.1]

private theorem fubini_fixed_line_denom_left_ne_v4
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ((c : ℂ) + (t : ℂ) * I) - ρ.val ≠ 0 :=
  sub_ne_zero.mpr (fubini_fixed_line_left_ne_v4 c t ρ hc)

private theorem fubini_fixed_line_denom_right_ne_v4
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  apply fubini_one_sub_fixed_line_ne_v4 c t ρ hc
  rw [h]
  ring

private theorem fubini_paired_zero_kernel_continuous_v4
    (c : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    Continuous (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ) := by
  unfold WeilPairedZeroKernelV3
  have h₁ : Continuous
      (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I) - ρ.val) := by
    fun_prop
  have h₂ : Continuous
      (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val)) := by
    fun_prop
  exact
    (continuous_const.div h₁
      (fun t => fubini_fixed_line_denom_left_ne_v4 c t ρ hc)).add
      (continuous_const.div h₂
        (fun t => fubini_fixed_line_denom_right_ne_v4 c t ρ hc))

private theorem fubini_paired_zero_kernel_global_norm_bound_v4
    (c t : ℝ) (ρ : LiCriterion.NontrivialZero) (hc : 1 < c) :
    ‖WeilPairedZeroKernelV3 c t ρ‖ ≤ 2 / (c - 1) := by
  let δ : ℝ := c - 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let d₁ : ℂ := ((c : ℂ) + (t : ℂ) * I) - ρ.val
  let d₂ : ℂ := ((c : ℂ) + (t : ℂ) * I) - (1 - ρ.val)
  have hd₁ : δ ≤ ‖d₁‖ := by
    have hre : δ ≤ d₁.re := by
      dsimp [δ, d₁]
      simp
      linarith [ρ.property.2.2]
    exact hre.trans (Complex.re_le_norm d₁)
  have hd₂ : δ ≤ ‖d₂‖ := by
    have hre : δ ≤ d₂.re := by
      dsimp [δ, d₂]
      simp
      linarith [ρ.property.2.1]
    exact hre.trans (Complex.re_le_norm d₂)
  have hi₁ : ‖(1 : ℂ) / d₁‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ hd₁
  have hi₂ : ‖(1 : ℂ) / d₂‖ ≤ 1 / δ := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hδ hd₂
  change ‖(1 : ℂ) / d₁ + (1 : ℂ) / d₂‖ ≤ 2 / δ
  calc
    ‖(1 : ℂ) / d₁ + (1 : ℂ) / d₂‖
        ≤ ‖(1 : ℂ) / d₁‖ + ‖(1 : ℂ) / d₂‖ := norm_add_le _ _
    _ ≤ 1 / δ + 1 / δ := add_le_add hi₁ hi₂
    _ = 2 / δ := by ring

private theorem fubini_paired_zero_kernel_mul_integrable_v4
    (H : ℝ → ℂ) (c : ℝ) (ρ : LiCriterion.NontrivialZero)
    (hc : 1 < c) (hH : HasVerticalNormMomentsTwoV3 H) :
    Integrable (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ * H t) := by
  have hkmeas :
      AEStronglyMeasurable (fun t : ℝ => WeilPairedZeroKernelV3 c t ρ) :=
    (fubini_paired_zero_kernel_continuous_v4 c ρ hc).aestronglyMeasurable
  exact hH.1.bdd_mul hkmeas
    (Filter.Eventually.of_forall fun t =>
      fubini_paired_zero_kernel_global_norm_bound_v4 c t ρ hc)

/-- The FZ certificate is exactly strong enough to commute the multiplicity-
weighted paired zero series with the fixed-line integral. -/
theorem riemannXi_paired_kernel_integral_tsum_v4
    (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    (∑' ρ : LiCriterion.NontrivialZero,
      ∫ t : ℝ,
        ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
          WeilPairedZeroKernelV3 c t ρ) * H t) =
      ∫ t : ℝ,
        ∑' ρ : LiCriterion.NontrivialZero,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t := by
  apply integral_tsum_of_summable_integral_norm
  · intro ρ
    have hprod :=
      fubini_paired_zero_kernel_mul_integrable_v4 H c ρ hc hH
    simpa [mul_assoc] using
      hprod.const_mul
        (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ)
  · have hFZ :=
      riemannXi_paired_kernel_product_integral_summable_v3 H c hc hH
    refine hFZ.congr ?_
    intro ρ
    have heq :
        (fun t : ℝ =>
          ‖((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              WeilPairedZeroKernelV3 c t ρ) * H t‖) =
        (fun t : ℝ =>
          (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℝ) *
            ‖WeilPairedZeroKernelV3 c t ρ * H t‖) := by
      funext t
      simp [norm_mul, mul_assoc]
    rw [heq, integral_const_mul]

/-- Full analytic composition achieved by the current fixed-line lane:
the integral of the paired xi logarithmic derivative is the multiplicity-
weighted series of paired-kernel integrals. -/
theorem riemannXi_paired_logDeriv_fixed_line_integral_v4
    (H : ℝ → ℂ) (c : ℝ) (hc : 1 < c)
    (hH : HasVerticalNormMomentsTwoV3 H) :
    (∫ t : ℝ,
      (2 * _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I)) * H t) =
      ∑' ρ : LiCriterion.NontrivialZero,
        ∫ t : ℝ,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t := by
  calc
    (∫ t : ℝ,
      (2 * _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I)) * H t)
        =
      ∫ t : ℝ,
        ∑' ρ : LiCriterion.NontrivialZero,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t := by
      apply integral_congr_ae
      filter_upwards [] with t
      let s : ℂ := (c : ℂ) + (t : ℂ) * I
      have hs : ∀ ρ : LiCriterion.NontrivialZero, s ≠ ρ.val := by
        intro ρ
        exact fubini_fixed_line_left_ne_v4 c t ρ hc
      have h1s : ∀ ρ : LiCriterion.NontrivialZero, 1 - s ≠ ρ.val := by
        intro ρ
        exact fubini_one_sub_fixed_line_ne_v4 c t ρ hc
      have hsum :=
        riemannXi_paired_hadamard_kernel_summable_v2 s hs h1s
      have hts :=
        riemannXi_paired_hadamard_kernel_tsum_v2 s hs h1s
      calc
        (2 * _root_.logDeriv LiCriterion.riemannXi s) * H t
            =
          (∑' ρ : LiCriterion.NontrivialZero,
            (analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              (1 / (s - ρ.val) + 1 / (s - (1 - ρ.val)))) * H t := by
              rw [hts]
        _ =
          ∑' ρ : LiCriterion.NontrivialZero,
            ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
              WeilPairedZeroKernelV3 c t ρ) * H t := by
              rw [← hsum.tsum_mul_right (H t)]
              apply tsum_congr
              intro ρ
              rfl
    _ =
      ∑' ρ : LiCriterion.NontrivialZero,
        ∫ t : ℝ,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) * H t :=
      (riemannXi_paired_kernel_integral_tsum_v4 H c hc hH).symm

end

#print axioms riemannXi_paired_kernel_integral_tsum_v4
#print axioms riemannXi_paired_logDeriv_fixed_line_integral_v4
