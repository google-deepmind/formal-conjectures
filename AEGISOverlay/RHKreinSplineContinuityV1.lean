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

import AEGISOverlay.RHKreinSplineSupportV1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Continuity of the genuine order-19 spline

Convolution by a normalized interval is a difference of two primitives of
an integrable function. This proves continuity of the concrete spline
without assuming continuity of the interval indicator.
-/

open Set MeasureTheory FourierTransform Convolution

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineContinuityV1

open AEGIS.RHKreinSplineSupportV1 AEGIS.RHBoxFourierComplementarityV1

/-- A convolution with the normalized box is its moving interval average. -/
theorem convolution_normalizedBox (f : ℝ → ℂ) {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) x =
      (h : ℂ)⁻¹ * ∫ u in (x - h / 2)..(x + h / 2), f u := by
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  have he : (fun u => f u * normalizedBox h (x - u)) =
      (fun u => (h : ℂ)⁻¹ * (Ico (x - h / 2) (x + h / 2)).indicator f u) := by
    funext u
    by_cases hu : u ∈ Ico (x - h / 2) (x + h / 2)
    · have hv : x - u ∈ Ioc (-(h / 2)) (h / 2) := by
        constructor <;> linarith [hu.1, hu.2]
      simp [normalizedBox, boxProfile, hu, hv, mul_comm]
    · have hv : x - u ∉ Ioc (-(h / 2)) (h / 2) := by
        intro hv
        exact hu ⟨by linarith [hv.2], by linarith [hv.1]⟩
      simp [normalizedBox, boxProfile, hu, hv]
  rw [he, integral_const_mul, integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : x - h / 2 ≤ x + h / 2)]

/-- A single averaging step sends every integrable function to a continuous function. -/
theorem continuous_convolution_normalizedBox (f : ℝ → ℂ) (hf : Integrable f)
    {h : ℝ} (hh : 0 ≤ h) :
    Continuous (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) := by
  have he : (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) =
      (fun x => (h : ℂ)⁻¹ *
        ((∫ u in (0 : ℝ)..(x + h / 2), f u) -
          ∫ u in (0 : ℝ)..(x - h / 2), f u)) := by
    funext x
    rw [convolution_normalizedBox f hh x,
      intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable]
  rw [he]
  exact continuous_const.mul
    (((hf.continuous_primitive 0).comp (continuous_id.add_const (h / 2))).sub
      ((hf.continuous_primitive 0).comp (continuous_id.sub continuous_const)))

/-- The actual order-19 spline satisfies the continuity hypothesis of Krein pairing. -/
theorem spline19_continuous (L : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    Continuous (spline19 L h) := by
  have hc : Continuous (splineCore h 18) :=
    continuous_convolution_normalizedBox (splineCore h 17) (splineCore_integrable h 17) hh
  exact hc.comp (continuous_id.sub continuous_const)

/-- An interval primitive gains one finite order of differentiability. -/
theorem primitive_contDiff (n : ℕ) (f : ℝ → ℂ) (hf : ContDiff ℝ n f) :
    ContDiff ℝ (n + 1 : ℕ) (fun x => ∫ u in (0 : ℝ)..x, f u) := by
  rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 from rfl]
  refine contDiff_succ_iff_deriv.2
    ⟨intervalIntegral.differentiable_integral_of_continuous hf.continuous, by simp, ?_⟩
  have he : deriv (fun x => ∫ u in (0 : ℝ)..x, f u) = f := by
    funext x
    exact (hf.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.deriv
  rw [he]
  exact hf

/-- Every box averaging step gains one finite derivative. -/
theorem contDiff_convolution_normalizedBox (n : ℕ) (f : ℝ → ℂ)
    (hf : Integrable f) (hc : ContDiff ℝ n f) {h : ℝ} (hh : 0 ≤ h) :
    ContDiff ℝ (n + 1 : ℕ) (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) := by
  have he : (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) =
      (fun x => (h : ℂ)⁻¹ *
        ((∫ u in (0 : ℝ)..(x + h / 2), f u) -
          ∫ u in (0 : ℝ)..(x - h / 2), f u)) := by
    funext x
    rw [convolution_normalizedBox f hh x,
      intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable]
  rw [he]
  exact contDiff_const.mul
    (((primitive_contDiff n f hc).comp (contDiff_id.add contDiff_const)).sub
      ((primitive_contDiff n f hc).comp (contDiff_id.sub contDiff_const)))

/-- The convolution of `n+2` boxes has `n` continuous derivatives. -/
theorem splineCore_contDiff {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    ContDiff ℝ n (splineCore h (n + 1)) := by
  induction n with
  | zero =>
    exact contDiff_zero.2
      (continuous_convolution_normalizedBox (splineCore h 0) (splineCore_integrable h 0) hh)
  | succ n ih =>
    exact contDiff_convolution_normalizedBox n (splineCore h (n + 1))
      (splineCore_integrable h (n + 1)) ih hh

/-- The actual order-19 spline is `C^17`; it is not asserted to be smooth. -/
theorem spline19_contDiff (L : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ContDiff ℝ 17 (spline19 L h) := by
  have hc : ContDiff ℝ 17 (splineCore h 18) := splineCore_contDiff hh 17
  exact hc.comp (contDiff_id.sub contDiff_const)

end AEGIS.RHKreinSplineContinuityV1

#print axioms AEGIS.RHKreinSplineContinuityV1.convolution_normalizedBox
#print axioms AEGIS.RHKreinSplineContinuityV1.continuous_convolution_normalizedBox
#print axioms AEGIS.RHKreinSplineContinuityV1.spline19_continuous
#print axioms AEGIS.RHKreinSplineContinuityV1.spline19_contDiff
