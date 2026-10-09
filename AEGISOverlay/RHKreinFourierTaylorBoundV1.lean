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

import AEGISOverlay.RHKreinFiniteIntervalKernelV1
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic

/-!
# Fourier-moment control of the finite Krein Taylor remainder

The external order-19 certificate bounds the eighth derivative of its angular
Fourier correction by an exact time-domain moment.  This file proves the
general analytic bridge behind that step.

No certificate coefficients and no RH statement occur here.
-/

open MeasureTheory FourierTransform Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinFourierTaylorBoundV1

/-- Scale converting Mathlib frequency to the angular convention used by the
Krein certificate. -/
def angularScale : ℝ := -(2 * Real.pi)⁻¹

/-- Mathlib Fourier transform expressed in angular frequency. -/
def angularFourier (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  𝓕 f (angularScale * t)

/-- The algebraic scale is exactly the repository convention `-t/(2*pi)`. -/
theorem angularScale_mul (t : ℝ) :
    angularScale * t = -t / (2 * Real.pi) := by
  unfold angularScale
  field_simp [Real.pi_ne_zero]

/-- Integrable ordinary polynomial moments through order eight. -/
def HasMomentsUpToEight (f : ℝ → ℂ) : Prop :=
  ∀ n : ℕ, n ≤ 8 → Integrable (fun x : ℝ => x ^ n • f x)

set_option maxHeartbeats 2000000 in
/-- Every continuous compactly supported function has the finite polynomial
moments needed for the eighth-order Fourier Taylor argument. -/
theorem hasMomentsUpToEight_of_continuous_compact
    (f : ℝ → ℂ) (hc : Continuous f) (hs : HasCompactSupport f) :
    HasMomentsUpToEight f := by
  intro n _hn
  have hcont : Continuous (fun x : ℝ => x ^ n • f x) :=
    (continuous_id.pow n).smul hc
  have hs' : HasCompactSupport (fun x : ℝ => x ^ n • f x) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hs ⊢
    exact hs.mono fun x hx => by simp [hx]
  exact hcont.integrable_of_hasCompactSupport hs'

/-- Ordinary moments imply the norm moments required by Mathlib's Fourier
smoothness theorem. -/
theorem norm_moment_integrable
    (f : ℝ → ℂ) (h : HasMomentsUpToEight f)
    (n : ℕ) (hn : n ≤ 8) :
    Integrable (fun x : ℝ => ‖x‖ ^ n * ‖f x‖) := by
  have hi := (h n hn).norm
  simpa only [norm_smul, norm_pow] using hi

/-- The Fourier transform is C^8 under the committed moment hypothesis. -/
theorem fourier_contDiff_eight
    (f : ℝ → ℂ) (h : HasMomentsUpToEight f) :
    ContDiff ℝ 8 (𝓕 f) := by
  apply Real.contDiff_fourier
  intro n hn
  have hn' : n ≤ 8 := by exact_mod_cast hn
  exact norm_moment_integrable f h n hn'

/-- Exact eighth derivative formula before the angular rescaling. -/
theorem fourier_eighth_derivative
    (f : ℝ → ℂ) (h : HasMomentsUpToEight f) :
    iteratedDeriv 8 (𝓕 f) =
      𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8 • f x) := by
  apply Real.iteratedDeriv_fourier (N := (8 : ℕ∞))
  · intro n hn
    have hn' : n ≤ 8 := by exact_mod_cast hn
    exact h n hn'
  · norm_num

/-- Exact chain-rule identity for the angular Fourier transform. -/
theorem angular_eighth_derivative
    (f : ℝ → ℂ) (h : HasMomentsUpToEight f) :
    iteratedDeriv 8 (angularFourier f) =
      fun t : ℝ =>
        angularScale ^ 8 •
          𝓕 (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8 • f x)
            (angularScale * t) := by
  unfold angularFourier
  rw [iteratedDeriv_comp_const_smul (n := 8)
    (fourier_contDiff_eight f h) angularScale]
  rw [fourier_eighth_derivative f h]

/-- The eighth angular derivative is bounded by the L1 norm of the eighth
Fourier multiplier, with the exact angular scaling factor exposed. -/
theorem angular_eighth_derivative_norm_le
    (f : ℝ → ℂ) (h : HasMomentsUpToEight f) (t : ℝ) :
    ‖iteratedDeriv 8 (angularFourier f) t‖ ≤
      |angularScale| ^ 8 *
        ∫ x : ℝ, ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8) • f x‖ := by
  rw [angular_eighth_derivative f h]
  rw [norm_smul, Real.norm_eq_abs, abs_pow]
  apply mul_le_mul_of_nonneg_left
  · change ‖VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ ℝ)
      (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8 • f x)
      (angularScale * t)‖ ≤
        ∫ x : ℝ, ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8) • f x‖
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ)
      (fun x : ℝ => (-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8 • f x)
      (angularScale * t)
  · positivity

end AEGIS.RHKreinFourierTaylorBoundV1

#print axioms AEGIS.RHKreinFourierTaylorBoundV1.hasMomentsUpToEight_of_continuous_compact
#print axioms AEGIS.RHKreinFourierTaylorBoundV1.norm_moment_integrable
#print axioms AEGIS.RHKreinFourierTaylorBoundV1.fourier_contDiff_eight
#print axioms AEGIS.RHKreinFourierTaylorBoundV1.fourier_eighth_derivative
#print axioms AEGIS.RHKreinFourierTaylorBoundV1.angular_eighth_derivative
#print axioms AEGIS.RHKreinFourierTaylorBoundV1.angular_eighth_derivative_norm_le
