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

import AEGISOverlay.RHBoxFourierComplementarityV1
import Mathlib.Analysis.Fourier.Convolution

/-!
# The genuine convolution spline used in the Krein certificate

The order-19 cardinal spline is the convolution of nineteen normalized
interval indicators. This module proves its integrability, exact support
enclosure, and actual Mathlib Fourier transform at angular frequency.
The positive translated copy is supported on `[L, L + 19*h]` and its transform
is `exp(i*t*(L + 19*h/2)) * sinc(h*t/2)^19`.

These statements bind the certificate's spline convention to a genuine
function. They do not assert the differentiability or certificate inequality.
-/

open Set MeasureTheory FourierTransform Convolution
open scoped Pointwise

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineSupportV1

open AEGIS.RHBoxFourierComplementarityV1

/-- The interval density with integral one when `h > 0`. -/
def normalizedBox (h : ℝ) (x : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * boxProfile (h / 2) x

/-- `splineCore h n` has order `n+1`, so order nineteen is index eighteen. -/
def splineCore (h : ℝ) : ℕ → ℝ → ℂ
  | 0 => normalizedBox h
  | n + 1 => splineCore h n ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h

/-- The positive copy appearing in the rational order-19 certificate. -/
def spline19 (L h : ℝ) (x : ℝ) : ℂ :=
  splineCore h 18 (x - (L + 19 * h / 2))

theorem normalizedBox_integrable (h : ℝ) : Integrable (normalizedBox h) := by
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (-(h / 2)) (h / 2)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hb : Integrable (boxProfile (h / 2)) := by
    exact (hi.mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
  exact hb.const_mul _

theorem splineCore_integrable (h : ℝ) (n : ℕ) : Integrable (splineCore h n) := by
  induction n with
  | zero => exact normalizedBox_integrable h
  | succ n ih => exact ih.integrable_convolution _ (normalizedBox_integrable h)

theorem normalizedBox_support (h x : ℝ) (hx : normalizedBox h x ≠ 0) :
    x ∈ Icc (-(h / 2)) (h / 2) := by
  have hb : boxProfile (h / 2) x ≠ 0 := by
    intro hz
    exact hx (by simp [normalizedBox, hz])
  have hx' : x ∈ Ioc (-(h / 2)) (h / 2) := by
    by_contra hn
    exact hb (by simp [boxProfile, hn])
  exact ⟨hx'.1.le, hx'.2⟩

theorem splineCore_support (h : ℝ) (n : ℕ) (x : ℝ) (hx : splineCore h n x ≠ 0) :
    x ∈ Icc (-((n : ℝ) + 1) * h / 2) (((n : ℝ) + 1) * h / 2) := by
  induction n generalizing x with
  | zero =>
    simpa only [Nat.cast_zero, zero_add, neg_mul, one_mul, neg_div] using
      normalizedBox_support h x hx
  | succ n ih =>
    have hs := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ)
      (f := splineCore h n) (g := normalizedBox h) hx
    rcases hs with ⟨y, hy, z, hz, rfl⟩
    have hy' := ih y hy
    have hz' := normalizedBox_support h z hz
    simp only [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [hy'.1, hy'.2, hz'.1, hz'.2]

/-- Every finite normalized-box convolution has compact support in its
explicit interval enclosure. -/
theorem splineCore_hasCompactSupport (h : ℝ) (n : ℕ) :
    HasCompactSupport (splineCore h n) := by
  apply HasCompactSupport.intro
    (K := Icc (-((n : ℝ) + 1) * h / 2) (((n : ℝ) + 1) * h / 2))
    isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (splineCore_support h n x hn)

theorem spline19_support (L h x : ℝ) (hx : spline19 L h x ≠ 0) :
    x ∈ Icc L (L + 19 * h) := by
  have hs := splineCore_support h 18 (x - (L + 19 * h / 2)) hx
  norm_num at hs
  constructor <;> linarith [hs.1, hs.2]

theorem spline19_integrable (L h : ℝ) : Integrable (spline19 L h) := by
  exact (splineCore_integrable h 18).comp_sub_right (L + 19 * h / 2)

theorem spline19_hasCompactSupport (L h : ℝ) : HasCompactSupport (spline19 L h) := by
  apply HasCompactSupport.intro (K := Icc L (L + 19 * h)) isCompact_Icc
  intro x hx
  by_contra hn
  exact hx (spline19_support L h x hn)

private theorem fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem normalizedBox_fourier {h : ℝ} (hh : 0 < h) (t : ℝ) :
    𝓕 (normalizedBox h) (-t / (2 * Real.pi)) = (Real.sinc (h * t / 2) : ℂ) := by
  unfold normalizedBox
  rw [fourier_const_mul, fourier_boxProfile_scaled (by positivity : 0 ≤ h / 2)]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [show h / 2 * t = h * t / 2 by ring]
  push_cast
  field_simp [hh']

theorem splineCore_fourier {h : ℝ} (hh : 0 < h) (n : ℕ) (t : ℝ) :
    𝓕 (splineCore h n) (-t / (2 * Real.pi)) =
      (Real.sinc (h * t / 2) : ℂ) ^ (n + 1) := by
  induction n with
  | zero => simpa only [splineCore, zero_add, pow_one] using normalizedBox_fourier hh t
  | succ n ih =>
    rw [splineCore, Real.fourier_mul_convolution_eq (splineCore_integrable h n)
      (normalizedBox_integrable h), ih, normalizedBox_fourier hh t]
    exact (pow_succ _ (n + 1)).symm

private theorem angular_fourier (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f (-t / (2 * Real.pi)) =
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * f x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have he (x : ℝ) : -2 * Real.pi * x * (-t / (2 * Real.pi)) = t * x := by
    field_simp [Real.pi_ne_zero]
  simp only [he, smul_eq_mul]

theorem fourier_translate_angular (f : ℝ → ℂ) (c t : ℝ) :
    𝓕 (fun x => f (x - c)) (-t / (2 * Real.pi)) =
      Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) * 𝓕 f (-t / (2 * Real.pi)) := by
  rw [angular_fourier, angular_fourier]
  rw [← integral_add_right_eq_self
    (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * f (x - c)) c]
  simp only [add_sub_cancel_right]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [show (((t * (x + c) : ℝ) : ℂ) * Complex.I) =
    (((t * c : ℝ) : ℂ) * Complex.I) + (((t * x : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring, Complex.exp_add]
  ring

/-- The exact Fourier convention consumed by the order-19 certificate. -/
theorem spline19_fourier (L : ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    𝓕 (spline19 L h) (-t / (2 * Real.pi)) =
      Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
        (Real.sinc (h * t / 2) : ℂ) ^ 19 := by
  unfold spline19
  rw [fourier_translate_angular, splineCore_fourier hh]

/-- The convolution normalization gives total mass exactly one. -/
theorem spline19_integral (L : ℝ) {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, spline19 L h x) = 1 := by
  simpa [Real.fourier_real_eq_integral_exp_smul] using spline19_fourier L hh 0

/-- The certificate's spline vanishes throughout the forbidden open window. -/
theorem spline19_zero_in_window {L h : ℝ} (x : ℝ) (hx : |x| < L) :
    spline19 L h x = 0 := by
  by_contra hn
  have hs := (spline19_support L h x hn).1
  have ha := le_abs_self x
  linarith

/-- The five derivative columns use signs `+,+,-,-,+`. This is the exact
angular-frequency algebra; derivative regularity is a separate obligation. -/
theorem certificate_derivative_parity (j : Fin 5) (c t : ℝ) :
    (-1 : ℝ) ^ (j.val / 2) *
      (((-Complex.I * (t : ℂ)) ^ j.val) *
        Complex.exp (((t * c : ℝ) : ℂ) * Complex.I)).re =
      t ^ j.val * (if j.val % 2 = 0 then Real.cos (t * c) else Real.sin (t * c)) := by
  fin_cases j <;>
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

/-- The certificate's factor `1/2` exactly cancels the doubled real part from
Hermitian reflection, with the derivative parity signs included. -/
theorem certificate_reflected_derivative_parity (j : Fin 5) (c t : ℝ) :
    (((-1 : ℂ) ^ (j.val / 2) / 2) *
      (((-Complex.I * (t : ℂ)) ^ j.val) *
          Complex.exp (((t * c : ℝ) : ℂ) * Complex.I) +
        (starRingEnd ℂ) (((-Complex.I * (t : ℂ)) ^ j.val) *
          Complex.exp (((t * c : ℝ) : ℂ) * Complex.I)))).re =
      t ^ j.val * (if j.val % 2 = 0 then Real.cos (t * c) else Real.sin (t * c)) := by
  fin_cases j <;>
    norm_num [pow_succ, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im] <;>
    ring

end AEGIS.RHKreinSplineSupportV1

#print axioms AEGIS.RHKreinSplineSupportV1.splineCore_hasCompactSupport
#print axioms AEGIS.RHKreinSplineSupportV1.spline19_integrable
#print axioms AEGIS.RHKreinSplineSupportV1.spline19_support
#print axioms AEGIS.RHKreinSplineSupportV1.spline19_hasCompactSupport
#print axioms AEGIS.RHKreinSplineSupportV1.spline19_fourier
#print axioms AEGIS.RHKreinSplineSupportV1.spline19_integral
#print axioms AEGIS.RHKreinSplineSupportV1.certificate_derivative_parity
#print axioms AEGIS.RHKreinSplineSupportV1.certificate_reflected_derivative_parity
