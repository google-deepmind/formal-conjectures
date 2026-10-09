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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Fourier integrability of the concrete Krein spline

For every integer power at least two, `|sinc(x)|^n ≤ 2/(1+x²)`.
The rational majorant is integrable on the whole real line. Applying the
already-proved exact spline Fourier formula and its frequency scaling
establishes the actual Fourier-integrability hypothesis of Krein pairing.
-/

open MeasureTheory FourierTransform

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineFourierIntegrableV1

open AEGIS.RHKreinSplineSupportV1

/-- A global integrable rational majorant for every sinc power of order at least two. -/
theorem sinc_pow_rational_bound (n : ℕ) (hn : 2 ≤ n) (x : ℝ) :
    |Real.sinc x| ^ n ≤ 2 / (1 + x ^ 2) := by
  have hs : (Real.sinc x) ^ 2 ≤ 1 := by
    simpa only [sq_abs] using
      (pow_le_one₀ (abs_nonneg (Real.sinc x)) (Real.abs_sinc_le_one x) :
        |Real.sinc x| ^ 2 ≤ 1)
  have hi : x * Real.sinc x = Real.sin x := by
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.sinc_of_ne_zero hx]
      field_simp
  have hi2 : x ^ 2 * (Real.sinc x) ^ 2 = (Real.sin x) ^ 2 := by
    calc
      x ^ 2 * (Real.sinc x) ^ 2 = (x * Real.sinc x) ^ 2 := by ring
      _ = (Real.sin x) ^ 2 := by rw [hi]
  have hsin : (Real.sin x) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (Real.cos x)]
  have hsbound : (Real.sinc x) ^ 2 ≤ 2 / (1 + x ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).2
    nlinarith
  have hk : |Real.sinc x| ^ (n - 2) ≤ 1 :=
    pow_le_one₀ (abs_nonneg (Real.sinc x)) (Real.abs_sinc_le_one x)
  calc
    |Real.sinc x| ^ n = |Real.sinc x| ^ 2 * |Real.sinc x| ^ (n - 2) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ |Real.sinc x| ^ 2 * 1 := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ = (Real.sinc x) ^ 2 := by rw [mul_one, sq_abs]
    _ ≤ 2 / (1 + x ^ 2) := hsbound

/-- The sinc powers are integrable with respect to Lebesgue measure, not just
on a finite interval. -/
theorem sinc_pow_integrable (n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x : ℝ => (Real.sinc x : ℂ) ^ n) := by
  refine (integrable_inv_one_add_sq.const_mul (2 : ℝ)).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp Real.continuous_sinc).pow n).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv] using
        sinc_pow_rational_bound n hn x)

/-- Polynomially weighted sinc powers remain integrable when two powers
remain after cancelling against the polynomial weight. -/
theorem weighted_sinc_pow_integrable (j n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun x : ℝ => (x : ℂ) ^ j * (Real.sinc x : ℂ) ^ (j + n)) := by
  have he (x : ℝ) : (x : ℂ) * (Real.sinc x : ℂ) = (Real.sin x : ℂ) := by
    have hr : x * Real.sinc x = Real.sin x := by
      by_cases hx : x = 0
      · simp [hx]
      · rw [Real.sinc_of_ne_zero hx]
        field_simp
    exact_mod_cast hr
  have hf : (fun x : ℝ => (x : ℂ) ^ j * (Real.sinc x : ℂ) ^ (j + n)) =
      (fun x : ℝ => (Real.sin x : ℂ) ^ j * (Real.sinc x : ℂ) ^ n) := by
    funext x
    rw [pow_add, ← mul_assoc, ← mul_pow, he]
  rw [hf]
  refine (sinc_pow_integrable n hn).norm.mono' ?_ ?_
  · have hc : Continuous (fun x : ℝ =>
        (Real.sin x : ℂ) ^ j * (Real.sinc x : ℂ) ^ n) := by fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      rw [norm_mul]
      have hb : ‖(Real.sin x : ℂ) ^ j‖ ≤ 1 := by
        simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using
          (pow_le_one₀ (abs_nonneg (Real.sin x)) (Real.abs_sin_le_one x) :
            |Real.sin x| ^ j ≤ 1)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hb
        (norm_nonneg ((Real.sinc x : ℂ) ^ n)))

/-- The polynomially weighted integrability is preserved under any nonzero scale. -/
theorem weighted_sinc_scaled_integrable (a : ℝ) (ha : a ≠ 0)
    (j n : ℕ) (hn : 2 ≤ n) :
    Integrable (fun t : ℝ => (t : ℂ) ^ j * (Real.sinc (a * t) : ℂ) ^ (j + n)) := by
  have hi := (weighted_sinc_pow_integrable j n hn).comp_mul_left' ha
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hi' := hi.const_mul ((a : ℂ)⁻¹ ^ j)
  convert hi' using 1
  funext t
  simp only [Complex.ofReal_mul]
  rw [← mul_assoc, ← mul_pow]
  rw [← mul_assoc, inv_mul_cancel₀ hac, one_mul]

/-- Integrability at angular frequency follows from the exact Fourier formula. -/
theorem spline19_fourier_scaled_integrable (L : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (fun t : ℝ => 𝓕 (spline19 L h) (-t / (2 * Real.pi))) := by
  have hs : Integrable (fun t : ℝ => (Real.sinc (h * t / 2) : ℂ) ^ 19) := by
    have hh2 : h / 2 ≠ 0 := by positivity
    simpa only [div_mul_eq_mul_div] using
      (sinc_pow_integrable 19 (by norm_num)).comp_mul_left' hh2
  have he : (fun t : ℝ => 𝓕 (spline19 L h) (-t / (2 * Real.pi))) =
      (fun t => Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
        (Real.sinc (h * t / 2) : ℂ) ^ 19) := funext (spline19_fourier L hh)
  rw [he]
  refine hs.norm.mono' ?_ ?_
  · have hc : Continuous (fun t : ℝ =>
        Complex.exp (((t * (L + 19 * h / 2) : ℝ) : ℂ) * Complex.I) *
          (Real.sinc (h * t / 2) : ℂ) ^ 19) := by
      fun_prop
    exact hc.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      simp [Complex.norm_exp])

/-- The actual Mathlib Fourier transform of the genuine order-19 spline is integrable. -/
theorem spline19_fourier_integrable (L : ℝ) {h : ℝ} (hh : 0 < h) :
    Integrable (𝓕 (spline19 L h)) := by
  have hp : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hi := (spline19_fourier_scaled_integrable L hh).comp_mul_right' hp
  convert hi using 1
  funext ξ
  field_simp [Real.pi_ne_zero]

end AEGIS.RHKreinSplineFourierIntegrableV1

#print axioms AEGIS.RHKreinSplineFourierIntegrableV1.sinc_pow_rational_bound
#print axioms AEGIS.RHKreinSplineFourierIntegrableV1.sinc_pow_integrable
#print axioms AEGIS.RHKreinSplineFourierIntegrableV1.spline19_fourier_integrable
