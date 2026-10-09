import WeilFixedLineFubiniSwapV4
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — concrete paired Mellin fixed-line profile v5.

#543 closes the abstract FZ/Fubini assembly for an arbitrary vertical profile H
satisfying L1 moments through order two.  This module binds that abstract H to
the actual paired Mellin profile used in the fixed-line proof:

  H_f,c(t) = M f(c+it) + M f(1-c-it).

The second summand is the vertical line 1-c composed with t ↦ -t.  Lebesgue
measure is invariant under negation, so the already kernel-verified Schwartz
moment bounds transfer directly.

No kernel integral evaluation, gamma/digamma normalization, arithmetic sign,
global Weil positivity, or RH conclusion is asserted here.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section

/-- The exact paired Mellin profile appearing in the fixed-line Hadamard proof. -/
def WeilPairedMellinProfileV5
    (f : WeilCompactSmoothGV1) (c t : ℝ) : ℂ :=
  mellin f.1 ((c : ℂ) + (t : ℂ) * I) +
    mellin f.1 (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)

/-- Algebraic identification with F(s)+F(1-s) on the line s=c+it. -/
theorem weil_paired_mellin_profile_eq_one_sub_v5
    (f : WeilCompactSmoothGV1) (c t : ℝ) :
    WeilPairedMellinProfileV5 f c t =
      mellin f.1 ((c : ℂ) + (t : ℂ) * I) +
        mellin f.1 (1 - ((c : ℂ) + (t : ℂ) * I)) := by
  unfold WeilPairedMellinProfileV5
  congr 2
  push_cast
  ring

private theorem paired_mellin_line_neg_integrable_v5
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    Integrable (fun t : ℝ =>
      mellin f.1 ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
  have h : Integrable (fun t : ℝ =>
      mellin f.1 ((σ : ℂ) + (t : ℂ) * I)) := by
    exact weil_compact_smooth_mellin_vertical_integrable_all_v1 f σ
  have hcomp :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable h
  simpa [Function.comp_def] using hcomp

private theorem paired_mellin_line_neg_abs_moment_one_v5
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    Integrable (fun t : ℝ =>
      |t| * ‖mellin f.1 ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖) := by
  have h := weil_compact_smooth_mellin_vertical_abs_moment_one_v2 f σ
  have hcomp :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable h
  simpa [Function.comp_def] using hcomp

private theorem paired_mellin_line_neg_abs_moment_two_v5
    (f : WeilCompactSmoothGV1) (σ : ℝ) :
    Integrable (fun t : ℝ =>
      |t| ^ 2 * ‖mellin f.1 ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖) := by
  have h := weil_compact_smooth_mellin_vertical_abs_moment_two_v3 f σ
  have hcomp :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable h
  simpa [Function.comp_def] using hcomp

/-- The concrete paired Mellin profile satisfies exactly the abstract
A0/A1/A2 contract consumed by the fixed-line FZ/Fubini theorem. -/
theorem weil_paired_mellin_profile_has_vertical_norm_moments_two_v5
    (f : WeilCompactSmoothGV1) (c : ℝ) :
    HasVerticalNormMomentsTwoV3 (WeilPairedMellinProfileV5 f c) := by
  let F₁ : ℝ → ℂ := fun t =>
    mellin f.1 ((c : ℂ) + (t : ℂ) * I)
  let F₂ : ℝ → ℂ := fun t =>
    mellin f.1 (((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)

  have h0₁ : Integrable F₁ := by
    dsimp [F₁]
    exact weil_compact_smooth_mellin_vertical_integrable_all_v1 f c
  have h0₂ : Integrable F₂ := by
    dsimp [F₂]
    exact paired_mellin_line_neg_integrable_v5 f (1 - c)
  have h0 : Integrable (WeilPairedMellinProfileV5 f c) := by
    apply (h0₁.add h0₂).congr
    filter_upwards [] with t
    rfl

  have h1₁ : Integrable (fun t : ℝ => |t| * ‖F₁ t‖) := by
    dsimp [F₁]
    exact weil_compact_smooth_mellin_vertical_abs_moment_one_v2 f c
  have h1₂ : Integrable (fun t : ℝ => |t| * ‖F₂ t‖) := by
    dsimp [F₂]
    exact paired_mellin_line_neg_abs_moment_one_v5 f (1 - c)
  have h1major :
      Integrable (fun t : ℝ => |t| * ‖F₁ t‖ + |t| * ‖F₂ t‖) :=
    h1₁.add h1₂
  have h1meas :
      AEStronglyMeasurable
        (fun t : ℝ => |t| * ‖WeilPairedMellinProfileV5 f c t‖) := by
    exact continuous_abs.aestronglyMeasurable.mul h0.norm.aestronglyMeasurable
  have h1 :
      Integrable (fun t : ℝ =>
        |t| * ‖WeilPairedMellinProfileV5 f c t‖) := by
    refine h1major.mono' h1meas
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg _))]
    have htri : ‖F₁ t + F₂ t‖ ≤ ‖F₁ t‖ + ‖F₂ t‖ := norm_add_le _ _
    have hmul := mul_le_mul_of_nonneg_left htri (abs_nonneg t)
    simpa [WeilPairedMellinProfileV5, F₁, F₂, mul_add] using hmul

  have h2₁ : Integrable (fun t : ℝ => |t| ^ 2 * ‖F₁ t‖) := by
    dsimp [F₁]
    exact weil_compact_smooth_mellin_vertical_abs_moment_two_v3 f c
  have h2₂ : Integrable (fun t : ℝ => |t| ^ 2 * ‖F₂ t‖) := by
    dsimp [F₂]
    exact paired_mellin_line_neg_abs_moment_two_v5 f (1 - c)
  have h2major :
      Integrable (fun t : ℝ =>
        |t| ^ 2 * ‖F₁ t‖ + |t| ^ 2 * ‖F₂ t‖) :=
    h2₁.add h2₂
  have h2meas :
      AEStronglyMeasurable
        (fun t : ℝ => |t| ^ 2 *
          ‖WeilPairedMellinProfileV5 f c t‖) := by
    exact (continuous_abs.pow 2).aestronglyMeasurable.mul
      h0.norm.aestronglyMeasurable
  have h2 :
      Integrable (fun t : ℝ =>
        |t| ^ 2 * ‖WeilPairedMellinProfileV5 f c t‖) := by
    refine h2major.mono' h2meas
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg |t|) (norm_nonneg _))]
    have htri : ‖F₁ t + F₂ t‖ ≤ ‖F₁ t‖ + ‖F₂ t‖ := norm_add_le _ _
    have hmul := mul_le_mul_of_nonneg_left htri (sq_nonneg |t|)
    simpa [WeilPairedMellinProfileV5, F₁, F₂, mul_add] using hmul

  exact ⟨h0, h1, h2⟩

/-- Concrete specialization of #543's abstract fixed-line assembly to the
actual paired Mellin profile F(s)+F(1-s). -/
theorem riemannXi_paired_mellin_logDeriv_fixed_line_integral_v5
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
      (2 * _root_.logDeriv LiCriterion.riemannXi
        ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t) =
      ∑' ρ : LiCriterion.NontrivialZero,
        ∫ t : ℝ,
          ((analyticOrderNatAt LiCriterion.riemannXi ρ.val : ℂ) *
            WeilPairedZeroKernelV3 c t ρ) *
              WeilPairedMellinProfileV5 f c t := by
  exact riemannXi_paired_logDeriv_fixed_line_integral_v4
    (WeilPairedMellinProfileV5 f c) c hc
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c)

end

#print axioms weil_paired_mellin_profile_eq_one_sub_v5
#print axioms weil_paired_mellin_profile_has_vertical_norm_moments_two_v5
#print axioms riemannXi_paired_mellin_logDeriv_fixed_line_integral_v5
