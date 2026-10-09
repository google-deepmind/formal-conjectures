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

import AEGISOverlay.RHKreinSplineContinuityV1
import AEGISOverlay.RHKreinSplineFourierIntegrableV1
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Genuine derivative columns for the order-19 Krein spline

The concrete spline is C17. Every derivative through order seventeen is
continuous, compactly supported on the same interval, integrable, and has
an integrable Fourier transform. Its exact angular Fourier multiplier is
`(-i*t)^j`. In particular these statements cover all five derivative columns
used in the rational certificate. No distributional derivative is used.
-/

open Set MeasureTheory FourierTransform

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineDerivativesV1

open AEGIS.RHKreinSplineSupportV1 AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineFourierIntegrableV1

theorem spline19_derivative_contDiff (L : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (hj : j ≤ 17) :
    ContDiff ℝ (17 - j : ℕ) (deriv^[j] (spline19 L h)) := by
  apply ContDiff.iterate_deriv' (17 - j) j
  simpa [Nat.sub_add_cancel hj] using spline19_contDiff L hh

private theorem compact_derivative_iterate (f : ℝ → ℂ) (hf : HasCompactSupport f) (j : ℕ) :
    HasCompactSupport (deriv^[j] f) := by
  induction j with
  | zero => exact hf
  | succ j ih => simpa only [Function.iterate_succ_apply'] using ih.deriv

private theorem tsupport_derivative_iterate (f : ℝ → ℂ) (j : ℕ) :
    tsupport (deriv^[j] f) ⊆ tsupport f := by
  induction j with
  | zero => exact Subset.rfl
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using tsupport_deriv_subset.trans ih

/-- Every ordinary derivative remains supported on the same closed interval. -/
theorem spline19_derivative_support (L h : ℝ) (j : ℕ) :
    tsupport (deriv^[j] (spline19 L h)) ⊆ Icc L (L + 19 * h) := by
  apply (tsupport_derivative_iterate (spline19 L h) j).trans
  exact closure_minimal (fun x hx => spline19_support L h x hx) isClosed_Icc

/-- The certificate's derivative columns are integrable genuine functions. -/
theorem spline19_derivative_integrable (L : ℝ) {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (hj : j ≤ 17) :
    Integrable (deriv^[j] (spline19 L h)) :=
  (spline19_derivative_contDiff L hh j hj).continuous.integrable_of_hasCompactSupport
    (compact_derivative_iterate (spline19 L h) (spline19_hasCompactSupport L h) j)

/-- The exact angular Fourier formula for the actual ordinary derivatives. -/
theorem spline19_derivative_fourier (L : ℝ) {h : ℝ} (hh : 0 < h)
    (j : ℕ) (hj : j ≤ 17) (t : ℝ) :
    𝓕 (deriv^[j] (spline19 L h)) (-t / (2 * Real.pi)) =
      (-Complex.I * (t : ℂ)) ^ j *
        Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
          (Real.sinc (h * t / 2) : ℂ) ^ 19 := by
  revert hj
  induction j with
  | zero =>
    intro _
    simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using spline19_fourier L hh t
  | succ j ih =>
    intro hj
    have hj' : j ≤ 17 := by omega
    have hc1 : ContDiff ℝ 1 (deriv^[j] (spline19 L h)) :=
      (spline19_derivative_contDiff L hh.le j hj').of_le (by
        exact_mod_cast (show 1 ≤ 17 - j by omega))
    have hd : Differentiable ℝ (deriv^[j] (spline19 L h)) :=
      (contDiff_one_iff_deriv.mp hc1).1
    have hi := spline19_derivative_integrable L hh.le j hj'
    have hi' : Integrable (deriv (deriv^[j] (spline19 L h))) := by
      simpa only [Function.iterate_succ_apply'] using
        spline19_derivative_integrable L hh.le (j + 1) hj
    rw [Function.iterate_succ_apply', Real.fourier_deriv hi hd hi']
    dsimp only
    rw [ih hj']
    simp only [smul_eq_mul]
    have hr : 2 * Real.pi * (-t / (2 * Real.pi)) = -t := by
      field_simp [Real.pi_ne_zero]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) =
        -Complex.I * (t : ℂ) := by
      calc
        (2 * (Real.pi : ℂ) * Complex.I * ((-t / (2 * Real.pi) : ℝ) : ℂ)) =
            ((2 * Real.pi * (-t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        _ = (-t : ℝ) * Complex.I := by rw [hr]
        _ = -Complex.I * (t : ℂ) := by push_cast; ring
    rw [hc, pow_succ]
    ring

/-- All derivative columns consumed by the certificate have integrable Fourier
transforms; the stronger range `j ≤ 17` follows from the same sinc bound. -/
theorem spline19_derivative_fourier_integrable (L : ℝ) {h : ℝ} (hh : 0 < h)
    (j : ℕ) (hj : j ≤ 17) :
    Integrable (𝓕 (deriv^[j] (spline19 L h))) := by
  have hsum : j + (19 - j) = 19 := by omega
  have hs : Integrable (fun t : ℝ => (t : ℂ) ^ j * (Real.sinc (h * t / 2) : ℂ) ^ 19) := by
    have hh2 : h / 2 ≠ 0 := by positivity
    simpa only [hsum, div_mul_eq_mul_div] using
      weighted_sinc_scaled_integrable (h / 2) hh2 j (19 - j) (by omega)
  have he : (fun t : ℝ => 𝓕 (deriv^[j] (spline19 L h)) (-t / (2 * Real.pi))) =
      (fun t : ℝ => (-Complex.I * (t : ℂ)) ^ j *
        Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
          (Real.sinc (h * t / 2) : ℂ) ^ 19) :=
    funext (spline19_derivative_fourier L hh j hj)
  have hi : Integrable (fun t : ℝ =>
      𝓕 (deriv^[j] (spline19 L h)) (-t / (2 * Real.pi))) := by
    rw [he]
    refine hs.norm.mono' ?_ ?_
    · have hc : Continuous (fun t : ℝ => (-Complex.I * (t : ℂ)) ^ j *
          Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
            (Real.sinc (h * t / 2) : ℂ) ^ 19) := by fun_prop
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun t => by
        simp [norm_pow, Complex.norm_exp])
  have hp : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hi' := hi.comp_mul_right' hp
  convert hi' using 1
  funext ξ
  field_simp [Real.pi_ne_zero]

end AEGIS.RHKreinSplineDerivativesV1

#print axioms AEGIS.RHKreinSplineDerivativesV1.spline19_derivative_contDiff
#print axioms AEGIS.RHKreinSplineDerivativesV1.spline19_derivative_support
#print axioms AEGIS.RHKreinSplineDerivativesV1.spline19_derivative_integrable
#print axioms AEGIS.RHKreinSplineDerivativesV1.spline19_derivative_fourier
#print axioms AEGIS.RHKreinSplineDerivativesV1.spline19_derivative_fourier_integrable
