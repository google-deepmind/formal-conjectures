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

import AEGISOverlay.RHKreinSplineL1DerivativeBoundV1
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# L1 derivative bounds for the genuine normalized-box spline

The existing FTC identity is combined with translation invariance of Lebesgue
measure and the integral triangle inequality. Each differentiated averaging
step costs at most 2/h in L1. Induction gives the order-19 bounds through order
seventeen, with integrability proved, not inferred from a totalized integral.
The weighted eighth-moment bound supplies the spline part of the M8 budget.

No correction-function sign, finite-cell certificate, or RH is asserted.
AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Convolution

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineL1NormV1

open AEGIS.RHKreinSplineSupportV1
open AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineL1DerivativeBoundV1
open AEGIS.RHBoxFourierComplementarityV1

/-- The centered difference produced by differentiating one box average. -/
def boxDifference (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * (f (x + h / 2) - f (x - h / 2))

theorem boxDifference_integrable (h : ℝ) (f : ℝ → ℂ) (hf : Integrable f) :
    Integrable (boxDifference h f) :=
  ((hf.comp_add_right (h / 2)).sub (hf.comp_sub_right (h / 2))).const_mul _

/-- Translation invariance gives the precise L1 cost of the centered difference. -/
theorem integral_norm_boxDifference_le (f : ℝ → ℂ) (hf : Integrable f)
    {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, ‖boxDifference h f x‖) ≤ (2 / h) * ∫ x : ℝ, ‖f x‖ := by
  have hp := (hf.comp_add_right (h / 2)).norm
  have hm := (hf.comp_sub_right (h / 2)).norm
  calc
    (∫ x : ℝ, ‖boxDifference h f x‖) ≤
        ∫ x : ℝ, h⁻¹ * (‖f (x + h / 2)‖ + ‖f (x - h / 2)‖) := by
      apply integral_mono (boxDifference_integrable h f hf).norm
        ((hp.add hm).const_mul _)
      intro x
      dsimp only [boxDifference]
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hh.le)
    _ = (2 / h) * ∫ x : ℝ, ‖f x‖ := by
      rw [integral_const_mul, integral_add hp hm,
        integral_add_right_eq_self (fun x : ℝ => ‖f x‖) (h / 2),
        integral_sub_right_eq_self (fun x : ℝ => ‖f x‖) (h / 2)]
      ring

/-- The derivative is an integrable genuine function. -/
theorem deriv_convolution_normalizedBox_integrable (f : ℝ → ℂ)
    (hc : Continuous f) (hf : Integrable f) {h : ℝ} (hh : 0 < h) :
    Integrable (deriv (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h)) := by
  have he : deriv (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) =
      boxDifference h f := funext (deriv_convolution_normalizedBox f hc hh)
  rw [he]
  exact boxDifference_integrable h f hf

/-- The actual moving-average derivative, not a surrogate, has norm at most 2/h. -/
theorem integral_norm_deriv_convolution_normalizedBox_le (f : ℝ → ℂ)
    (hc : Continuous f) (hf : Integrable f) {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, ‖deriv (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) x‖) ≤
      (2 / h) * ∫ x : ℝ, ‖f x‖ := by
  have he : deriv (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) =
      boxDifference h f := funext (deriv_convolution_normalizedBox f hc hh)
  rw [he]
  exact integral_norm_boxDifference_le f hf hh

/-- Integral triangle inequality followed by Fubini, with both factors integrable. -/
theorem integral_norm_convolution_le (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
      (∫ x : ℝ, ‖f x‖) * ∫ x : ℝ, ‖g x‖ := by
  calc
    (∫ x : ℝ, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x‖) ≤
        ∫ x : ℝ, ((fun y => ‖f y‖) ⋆[ContinuousLinearMap.mul ℝ ℝ]
          (fun y => ‖g y‖)) x := by
      apply integral_mono (hf.integrable_convolution _ hg).norm
        (hf.norm.integrable_convolution _ hg.norm)
      intro x
      simpa only [convolution_def, ContinuousLinearMap.mul_apply', norm_mul] using
        norm_integral_le_integral_norm (fun t : ℝ => f t * g (x - t))
    _ = (∫ x : ℝ, ‖f x‖) * ∫ x : ℝ, ‖g x‖ := by
      simpa only [ContinuousLinearMap.mul_apply'] using
        integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf.norm hg.norm

/-- The normalized interval density has L1 mass exactly one. -/
theorem integral_norm_normalizedBox {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, ‖normalizedBox h x‖) = 1 := by
  have he : (fun x : ℝ => ‖normalizedBox h x‖) =
      (Ioc (-(h / 2)) (h / 2)).indicator (fun _ : ℝ => h⁻¹) := by
    funext x
    by_cases hx : x ∈ Ioc (-(h / 2)) (h / 2)
    · simp [normalizedBox, boxProfile, hx, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hh]
    · simp [normalizedBox, boxProfile, hx]
  rw [he, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(h / 2) ≤ h / 2),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  convert mul_inv_cancel₀ hh.ne' using 1
  ring

/-- All normalized-box convolution powers have L1 norm at most one. -/
theorem integral_norm_splineCore_le_one {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∫ x : ℝ, ‖splineCore h n x‖) ≤ 1 := by
  induction n with
  | zero =>
    exact le_of_eq (integral_norm_normalizedBox hh)
  | succ n ih =>
    calc
      (∫ x : ℝ, ‖splineCore h (n + 1) x‖) ≤
          (∫ x : ℝ, ‖splineCore h n x‖) * ∫ x : ℝ, ‖normalizedBox h x‖ :=
        integral_norm_convolution_le _ _ (splineCore_integrable h n)
          (normalizedBox_integrable h)
      _ ≤ 1 := by rw [integral_norm_normalizedBox hh, mul_one]; exact ih

/-- Finite-order differentiation commutes with the centered difference. -/
theorem iteratedDeriv_boxDifference (j : ℕ) (f : ℝ → ℂ)
    (hc : ContDiff ℝ j f) (h : ℝ) :
    iteratedDeriv j (boxDifference h f) = boxDifference h (iteratedDeriv j f) := by
  have hp : ContDiff ℝ j (fun y : ℝ => f (y + h / 2)) :=
    hc.comp (contDiff_id.add contDiff_const)
  have hm : ContDiff ℝ j (fun y : ℝ => f (y - h / 2)) :=
    hc.comp (contDiff_id.sub contDiff_const)
  funext x
  unfold boxDifference
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_sub hp.contDiffAt hm.contDiffAt,
    iteratedDeriv_comp_add_const j f (h / 2), iteratedDeriv_comp_sub_const j f (h / 2)]

/-- Each derivative consumes one box; two undifferentiated boxes remain.
The integrability component prevents vacuous use of totalized Bochner integrals. -/
theorem splineCore_iteratedDeriv_L1 {h : ℝ} (hh : 0 < h) (j n : ℕ) :
    Integrable (iteratedDeriv j (splineCore h (n + j + 1))) ∧
      (∫ x : ℝ, ‖iteratedDeriv j (splineCore h (n + j + 1)) x‖) ≤ (2 / h) ^ j := by
  induction j with
  | zero =>
    simpa only [iteratedDeriv_zero, pow_zero] using
      (show Integrable (splineCore h (n + 0 + 1)) ∧
        (∫ x : ℝ, ‖splineCore h (n + 0 + 1) x‖) ≤ 1 from
        ⟨splineCore_integrable h _, integral_norm_splineCore_le_one hh _⟩)
  | succ j ih =>
    have hc : ContDiff ℝ j (splineCore h (n + j + 1)) :=
      (splineCore_contDiff hh.le (n + j)).of_le (by
        exact_mod_cast (show j ≤ n + j by omega))
    have he : deriv (splineCore h (n + (j + 1) + 1)) =
        boxDifference h (splineCore h (n + j + 1)) := by
      rw [show n + (j + 1) + 1 = (n + j + 1) + 1 by omega, splineCore]
      exact funext (deriv_convolution_normalizedBox _ hc.continuous hh)
    rw [iteratedDeriv_succ', he, iteratedDeriv_boxDifference j _ hc h]
    refine ⟨boxDifference_integrable h _ ih.1, ?_⟩
    calc
      (∫ x : ℝ, ‖boxDifference h (iteratedDeriv j (splineCore h (n + j + 1))) x‖) ≤
          (2 / h) * ∫ x : ℝ, ‖iteratedDeriv j (splineCore h (n + j + 1)) x‖ :=
        integral_norm_boxDifference_le _ ih.1 hh
      _ ≤ (2 / h) * (2 / h) ^ j :=
        mul_le_mul_of_nonneg_left ih.2 (by positivity)
      _ = (2 / h) ^ (j + 1) := (pow_succ' _ _).symm

/-- The genuine order-19 spline satisfies the L1 derivative budget through order 17. -/
theorem spline19_iteratedDeriv_L1 (L : ℝ) {h : ℝ} (hh : 0 < h)
    (j : ℕ) (hj : j ≤ 17) :
    Integrable (iteratedDeriv j (spline19 L h)) ∧
      (∫ x : ℝ, ‖iteratedDeriv j (spline19 L h) x‖) ≤ (2 / h) ^ j := by
  have hc := splineCore_iteratedDeriv_L1 hh j (17 - j)
  rw [show 17 - j + j + 1 = 18 by omega] at hc
  unfold spline19
  rw [iteratedDeriv_comp_sub_const]
  refine ⟨hc.1.comp_sub_right _, ?_⟩
  rw [integral_sub_right_eq_self
    (fun x : ℝ => ‖iteratedDeriv j (splineCore h 18) x‖) (L + 19 * h / 2)]
  exact hc.2

/-- The same budget in the derivative-iterate convention of the certificate. -/
theorem spline19_derivative_L1 (L : ℝ) {h : ℝ} (hh : 0 < h)
    (j : ℕ) (hj : j ≤ 17) :
    Integrable (deriv^[j] (spline19 L h)) ∧
      (∫ x : ℝ, ‖(deriv^[j] (spline19 L h)) x‖) ≤ (2 / h) ^ j := by
  simpa only [iteratedDeriv_eq_iterate] using spline19_iteratedDeriv_L1 L hh j hj

private theorem tsupport_iteratedDeriv_subset (f : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using tsupport_deriv_subset.trans ih

/-- The moment bound used for the eighth Fourier derivative of each spline column. -/
theorem spline19_derivative_weighted_eighth_L1 (L : ℝ) (hL : 0 ≤ L)
    {h : ℝ} (hh : 0 < h) (j : ℕ) (hj : j ≤ 17) :
    Integrable (fun x : ℝ => |x| ^ 8 * ‖(deriv^[j] (spline19 L h)) x‖) ∧
      (∫ x : ℝ, |x| ^ 8 * ‖(deriv^[j] (spline19 L h)) x‖) ≤
        (2 / h) ^ j * (L + 19 * h) ^ 8 := by
  let f : ℝ → ℂ := deriv^[j] (spline19 L h)
  obtain ⟨hi, hb⟩ := spline19_derivative_L1 L hh j hj
  have hs : tsupport f ⊆ Icc L (L + 19 * h) := by
    apply (show tsupport f ⊆ tsupport (spline19 L h) from by
      simpa only [f, iteratedDeriv_eq_iterate] using
        tsupport_iteratedDeriv_subset (spline19 L h) j).trans
    exact closure_minimal (fun x hx => spline19_support L h x hx) isClosed_Icc
  have hbound (x : ℝ) : |x| ^ 8 * ‖f x‖ ≤ (L + 19 * h) ^ 8 * ‖f x‖ := by
    by_cases hx : f x = 0
    · simp [hx]
    · have hxI := hs (subset_closure hx)
      have hx0 : 0 ≤ x := hL.trans hxI.1
      rw [abs_of_nonneg hx0]
      gcongr
      exact hxI.2
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x| ^ 8 * ‖f x‖) volume :=
    (continuous_abs.pow 8).aestronglyMeasurable.mul hi.norm.aestronglyMeasurable
  have hiw : Integrable (fun x : ℝ => |x| ^ 8 * ‖f x‖) := by
    refine (hi.norm.const_mul ((L + 19 * h) ^ 8)).mono' hmeas ?_
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound x)
  refine ⟨hiw, ?_⟩
  calc
    (∫ x : ℝ, |x| ^ 8 * ‖f x‖) ≤ ∫ x : ℝ, (L + 19 * h) ^ 8 * ‖f x‖ :=
      integral_mono hiw (hi.norm.const_mul _) hbound
    _ = (L + 19 * h) ^ 8 * ∫ x : ℝ, ‖f x‖ := integral_const_mul _ _
    _ ≤ (L + 19 * h) ^ 8 * (2 / h) ^ j :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (2 / h) ^ j * (L + 19 * h) ^ 8 := mul_comm _ _

/-- Exact spline-column constants used in the rational M8 payload.
This is not the full correction M8 theorem or the finite-cell certificate. -/
theorem certificate_spline_columns_weighted_eighth_L1 (j : Fin 5) :
    Integrable (fun x : ℝ => |x| ^ 8 *
      ‖(deriv^[j.val] (spline19 (4 / 5) (1 / 1000))) x‖) ∧
      (∫ x : ℝ, |x| ^ 8 * ‖(deriv^[j.val] (spline19 (4 / 5) (1 / 1000))) x‖) ≤
        (2000 : ℝ) ^ j.val * (819 / 1000 : ℝ) ^ 8 := by
  have hj : j.val ≤ 17 := by omega
  convert spline19_derivative_weighted_eighth_L1 (4 / 5) (by norm_num)
    (h := 1 / 1000) (by norm_num) j.val hj using 1
  norm_num

end AEGIS.RHKreinSplineL1NormV1

#print axioms AEGIS.RHKreinSplineL1NormV1.boxDifference_integrable
#print axioms AEGIS.RHKreinSplineL1NormV1.integral_norm_boxDifference_le
#print axioms AEGIS.RHKreinSplineL1NormV1.deriv_convolution_normalizedBox_integrable
#print axioms AEGIS.RHKreinSplineL1NormV1.integral_norm_deriv_convolution_normalizedBox_le
#print axioms AEGIS.RHKreinSplineL1NormV1.integral_norm_convolution_le
#print axioms AEGIS.RHKreinSplineL1NormV1.integral_norm_normalizedBox
#print axioms AEGIS.RHKreinSplineL1NormV1.integral_norm_splineCore_le_one
#print axioms AEGIS.RHKreinSplineL1NormV1.iteratedDeriv_boxDifference
#print axioms AEGIS.RHKreinSplineL1NormV1.splineCore_iteratedDeriv_L1
#print axioms AEGIS.RHKreinSplineL1NormV1.spline19_iteratedDeriv_L1
#print axioms AEGIS.RHKreinSplineL1NormV1.spline19_derivative_L1
#print axioms AEGIS.RHKreinSplineL1NormV1.spline19_derivative_weighted_eighth_L1
#print axioms AEGIS.RHKreinSplineL1NormV1.certificate_spline_columns_weighted_eighth_L1
