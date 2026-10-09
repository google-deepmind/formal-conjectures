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

import AEGISOverlay.RHKreinSplineFourierIntegrableV1
import AEGISOverlay.RHKreinSplineContinuityV1
import RHKreinPairingV13

/-!
# A triangular hat column at an arbitrary centre

`hatAt u` is the Hermitian pair of width-`1/50` triangles at `±u`.  It is continuous, integrable
with integrable Fourier transform, vanishes on `|x| < u - 1/50`, and
`Re 𝓕(hatAt u)(t/2π) = (2/50) sinc(t/100)² cos(t u)`.  This is the column of
`RHKreinExplicitCorrectionV1.hatColumn` with the centre as a parameter.  AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinHatAtV1

open AEGIS.RHKreinSplineSupportV1 AEGIS.RHKreinSplineContinuityV1
open AEGIS.RHKreinSplineFourierIntegrableV1

def reflectedAt (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x + (starRingEnd ℂ) (f (-x))

theorem fourier_add' (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (ξ : ℝ) : 𝓕 (fun x => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  exact congrArg (fun F : ℝ → ℂ => F ξ)
    (VectorFourier.fourierIntegral_add (e := Real.fourierChar)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg)

theorem fourier_const_mul' (f : ℝ → ℂ) (c : ℂ) (ξ : ℝ) :
    𝓕 (fun x => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem reflectedAt_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (reflectedAt f) := by
  have hi : Integrable (fun x : ℝ => (starRingEnd ℂ) (f (-x))) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hf.comp_neg
  exact hf.add hi

theorem reflectedAt_fourier {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (reflectedAt f) ξ = 𝓕 f ξ + (starRingEnd ℂ) (𝓕 f ξ) := by
  have hi : Integrable (fun x : ℝ => (starRingEnd ℂ) (f (-x))) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hf.comp_neg
  change 𝓕 (fun x : ℝ => f x + (starRingEnd ℂ) (f (-x))) ξ =
    𝓕 f ξ + (starRingEnd ℂ) (𝓕 f ξ)
  rw [fourier_add' f _ hf hi, AEGIS.RHKreinPairingV13.fourier_conj_neg]

theorem angular_integrable_iff' (f : ℝ → ℂ)
    (hf : Integrable (fun t : ℝ => f (-t / (2 * Real.pi)))) : Integrable f := by
  have hp : -(2 * Real.pi) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hi := hf.comp_mul_right' hp
  convert hi using 1
  funext ξ
  field_simp [Real.pi_ne_zero]

/-- One triangle of half-width `1/50` centred at `u`. -/
def posHatAt (u : ℝ) (x : ℝ) : ℂ :=
  (1 / 50 : ℂ) * splineCore (1 / 50) 1 (x - u)

theorem posHatAt_continuous (u : ℝ) : Continuous (posHatAt u) := by
  have hc := (splineCore_contDiff (by norm_num : (0 : ℝ) ≤ 1 / 50) 0).continuous
  exact continuous_const.mul (hc.comp (continuous_id.sub continuous_const))

theorem posHatAt_integrable (u : ℝ) : Integrable (posHatAt u) :=
  ((splineCore_integrable (1 / 50) 1).comp_sub_right u).const_mul _

theorem posHatAt_fourier (u t : ℝ) :
    𝓕 (posHatAt u) (-t / (2 * Real.pi)) =
      (1 / 50 : ℂ) * Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) *
        (Real.sinc (t / 100) : ℂ) ^ 2 := by
  unfold posHatAt
  rw [fourier_const_mul', fourier_translate_angular,
    splineCore_fourier (by norm_num : (0 : ℝ) < 1 / 50)]
  rw [show (1 / 50 : ℝ) * t / 2 = t / 100 by ring]
  ring

theorem posHatAt_fourier_integrable (u : ℝ) : Integrable (𝓕 (posHatAt u)) := by
  apply angular_integrable_iff'
  have hs : Integrable (fun t : ℝ => (Real.sinc (t / 100) : ℂ) ^ 2) := by
    simpa only [div_eq_mul_inv] using
      (sinc_pow_integrable 2 (by norm_num)).comp_mul_right' (by norm_num : (100 : ℝ)⁻¹ ≠ 0)
  have he : Integrable (fun t : ℝ =>
      Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (Real.sinc (t / 100) : ℂ) ^ 2) := by
    refine hs.norm.mono' ?_ ?_
    · have hc : Continuous (fun t : ℝ =>
          Complex.exp (((t * u : ℝ) : ℂ) * Complex.I) * (Real.sinc (t / 100) : ℂ) ^ 2) := by
        fun_prop
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by simp [Complex.norm_exp]
  exact (he.const_mul (1 / 50 : ℂ)).congr (Filter.Eventually.of_forall fun t => by
    simpa [mul_assoc] using (posHatAt_fourier u t).symm)

theorem posHatAt_zero (u : ℝ) {x : ℝ} (hx : x < u - 1 / 50) : posHatAt u x = 0 := by
  have hz : splineCore (1 / 50) 1 (x - u) = 0 := by
    by_contra hn
    have hs := (splineCore_support (1 / 50) 1 (x - u) hn).1
    norm_num at hs
    linarith
  have hz' : splineCore (50⁻¹ : ℝ) 1 (x - u) = 0 := by simpa only [one_div] using hz
  simp [posHatAt, one_div, hz']

/-- The Hermitian pair of triangles at `±u`. -/
def hatAt (u : ℝ) : ℝ → ℂ := reflectedAt (posHatAt u)

theorem hatAt_continuous (u : ℝ) : Continuous (hatAt u) :=
  (posHatAt_continuous u).add (continuous_conj.comp ((posHatAt_continuous u).comp continuous_neg))

theorem hatAt_integrable (u : ℝ) : Integrable (hatAt u) :=
  reflectedAt_integrable (posHatAt_integrable u)

theorem hatAt_fourier_integrable (u : ℝ) : Integrable (𝓕 (hatAt u)) := by
  have hF := posHatAt_fourier_integrable u
  have hi : Integrable (fun ξ : ℝ => (starRingEnd ℂ) (𝓕 (posHatAt u) ξ)) := by
    simpa using (Complex.conjLIE.toContinuousLinearMap).integrable_comp hF
  exact (hF.add hi).congr (Filter.Eventually.of_forall fun ξ =>
    (reflectedAt_fourier (posHatAt_integrable u) ξ).symm)

theorem hatAt_zero (u : ℝ) {x : ℝ} (hx : |x| < u - 1 / 50) : hatAt u x = 0 := by
  have h1 : x < u - 1 / 50 := lt_of_le_of_lt (le_abs_self x) hx
  have h2 : -x < u - 1 / 50 := lt_of_le_of_lt (neg_le_abs x) hx
  simp [hatAt, reflectedAt, posHatAt_zero u h1, posHatAt_zero u h2]

theorem hatAt_fourier_re_neg (u t : ℝ) :
    (𝓕 (hatAt u) (-t / (2 * Real.pi))).re =
      (2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * u) := by
  rw [hatAt, reflectedAt_fourier (posHatAt_integrable u), posHatAt_fourier]
  norm_num [← Complex.ofReal_pow, Complex.add_re, Complex.conj_re, Complex.mul_re,
    Complex.mul_im, Complex.exp_re]
  ring

/-- The form consumed by `RHKreinZetaBridgeV1`. -/
theorem hatAt_fourier_re (u t : ℝ) :
    (𝓕 (hatAt u) (t / (2 * Real.pi))).re =
      (2 / 50) * Real.sinc (t / 100) ^ 2 * Real.cos (t * u) := by
  have h := hatAt_fourier_re_neg u (-t)
  rw [show -(-t) / (2 * Real.pi) = t / (2 * Real.pi) by ring] at h
  rw [h, show -t / 100 = -(t / 100) by ring, Real.sinc_neg, neg_mul, Real.cos_neg]

end AEGIS.RHKreinHatAtV1

#print axioms AEGIS.RHKreinHatAtV1.hatAt_fourier_re
#print axioms AEGIS.RHKreinHatAtV1.hatAt_zero
#print axioms AEGIS.RHKreinHatAtV1.hatAt_fourier_integrable
