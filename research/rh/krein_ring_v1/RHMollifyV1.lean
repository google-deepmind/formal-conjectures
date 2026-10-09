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

import Mathlib

/-!
# Mollifier with a quantitative Fourier transform

`moll ε` is the normalized smooth bump on `(-ε, ε)` (Mathlib's `ContDiffBump.normed`).  It is
smooth, even, nonnegative, of integral `1`, so its Fourier transform is real and

  `‖𝓕 (moll ε) ξ − 1‖ ≤ (2π ε ξ)² / 2`.

Convolving an explicit column (spline, hat) with `moll ε` gives a `C^∞` compactly supported
function whose Fourier transform is the explicit one times a factor within `(2πεξ)²/2` of `1`:
the low-block entries of a Feshbach certificate become explicit integrals plus an `O(ε²)` error.
AUTHORITY_EFFECT = NONE.
-/

open MeasureTheory FourierTransform Complex
open scoped ContDiff
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMollifyV1

/-- The bump on `(-ε, ε)` with inner radius `ε/2`. -/
def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- The normalized real mollifier. -/
def mollR (ε : ℝ) (hε : 0 < ε) (x : ℝ) : ℝ := (bump ε hε).normed volume x

/-- The complex mollifier. -/
def moll (ε : ℝ) (hε : 0 < ε) (x : ℝ) : ℂ := (mollR ε hε x : ℂ)

theorem mollR_nonneg (ε : ℝ) (hε : 0 < ε) (x : ℝ) : 0 ≤ mollR ε hε x :=
  (bump ε hε).nonneg_normed x

theorem mollR_even (ε : ℝ) (hε : 0 < ε) (x : ℝ) : mollR ε hε (-x) = mollR ε hε x :=
  (bump ε hε).normed_neg x

theorem mollR_integral (ε : ℝ) (hε : 0 < ε) : ∫ x, mollR ε hε x = 1 :=
  (bump ε hε).integral_normed

theorem mollR_zero_outside (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : ε ≤ |x|) : mollR ε hε x = 0 := by
  have h := (bump ε hε).support_normed_eq (μ := volume)
  by_contra hne
  have hmem : x ∈ Function.support (mollR ε hε) := hne
  unfold mollR at hmem
  rw [h, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  have : (bump ε hε).rOut = ε := rfl
  rw [this] at hmem
  linarith

theorem mollR_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (mollR ε hε) :=
  (bump ε hε).continuous_normed

theorem mollR_integrable (ε : ℝ) (hε : 0 < ε) : Integrable (mollR ε hε) :=
  (mollR_continuous ε hε).integrable_of_hasCompactSupport (bump ε hε).hasCompactSupport_normed

theorem moll_contDiff (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (moll ε hε) :=
  Complex.ofRealCLM.contDiff.comp ((bump ε hε).contDiff_normed (n := ⊤))

theorem moll_hasCompactSupport (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (moll ε hε) :=
  (bump ε hε).hasCompactSupport_normed.comp_left Complex.ofReal_zero

/-- The quantitative Fourier estimate. -/
theorem fourier_moll_sub_one (ε : ℝ) (hε : 0 < ε) (ξ : ℝ) :
    ‖𝓕 (moll ε hε) ξ - 1‖ ≤ (2 * Real.pi * ε * ξ) ^ 2 / 2 := by
  set ρ := mollR ε hε with hρ
  have hρi := mollR_integrable ε hε
  -- 𝓕 ρ ξ = ∫ ρ x · e^{-2πixξ}
  have hF : 𝓕 (moll ε hε) ξ = ∫ x, (ρ x : ℂ) * Complex.exp (-(2 * Real.pi * x * ξ : ℝ) * I) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; funext x
    simp only [smul_eq_mul, moll, hρ]
    rw [mul_comm]; congr 2; push_cast; ring
  -- split into cos and sin parts
  have hcos_int : Integrable (fun x => ρ x * Real.cos (2 * Real.pi * x * ξ)) :=
    hρi.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hsin_int : Integrable (fun x => ρ x * Real.sin (2 * Real.pi * x * ξ)) :=
    hρi.mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hexp : ∀ x : ℝ, (ρ x : ℂ) * Complex.exp (-(2 * Real.pi * x * ξ : ℝ) * I) =
      ((ρ x * Real.cos (2 * Real.pi * x * ξ) : ℝ) : ℂ) -
        ((ρ x * Real.sin (2 * Real.pi * x * ξ) : ℝ) : ℂ) * I := by
    intro x
    rw [show (-(2 * Real.pi * x * ξ : ℝ) : ℂ) * I = ((-(2 * Real.pi * x * ξ) : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg]
    push_cast; ring
  have hsin0 : ∫ x, ρ x * Real.sin (2 * Real.pi * x * ξ) = 0 := by
    have h := integral_neg_eq_self (fun x => ρ x * Real.sin (2 * Real.pi * x * ξ)) volume
    have e : (fun x => ρ (-x) * Real.sin (2 * Real.pi * (-x) * ξ)) =
        fun x => -(ρ x * Real.sin (2 * Real.pi * x * ξ)) := by
      funext x
      rw [hρ, mollR_even, show 2 * Real.pi * (-x) * ξ = -(2 * Real.pi * x * ξ) by ring,
        Real.sin_neg]
      ring
    rw [e, integral_neg] at h
    linarith
  have hF2 : 𝓕 (moll ε hε) ξ = ((∫ x, ρ x * Real.cos (2 * Real.pi * x * ξ) : ℝ) : ℂ) := by
    rw [hF]
    simp_rw [hexp]
    have h1 : Integrable (fun x => ((ρ x * Real.cos (2 * Real.pi * x * ξ) : ℝ) : ℂ)) :=
      hcos_int.ofReal
    have h2 : Integrable (fun x => ((ρ x * Real.sin (2 * Real.pi * x * ξ) : ℝ) : ℂ) * I) :=
      hsin_int.ofReal.mul_const I
    rw [integral_sub h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hsin0]
    simp
  rw [hF2]
  have hone : (1 : ℂ) = ((∫ x, ρ x : ℝ) : ℂ) := by rw [hρ, mollR_integral]; simp
  rw [hone, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← integral_sub hcos_int hρi]
  -- |∫ ρ (cos − 1)| ≤ ∫ ρ (1 − cos) ≤ ∫ ρ (2πεξ)²/2
  have hpt : ∀ x, |ρ x * Real.cos (2 * Real.pi * x * ξ) - ρ x| ≤ ρ x * ((2 * Real.pi * ε * ξ) ^ 2 / 2) := by
    intro x
    have h0 := mollR_nonneg ε hε x
    by_cases hx : ε ≤ |x|
    · rw [hρ, mollR_zero_outside ε hε x hx]; simp
    · push_neg at hx
      have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * x * ξ)
      have hc1 := Real.cos_le_one (2 * Real.pi * x * ξ)
      have hsq : (2 * Real.pi * x * ξ) ^ 2 ≤ (2 * Real.pi * ε * ξ) ^ 2 := by
        have : (2 * Real.pi * x * ξ) ^ 2 = (2 * Real.pi * ξ) ^ 2 * x ^ 2 := by ring
        have h2 : (2 * Real.pi * ε * ξ) ^ 2 = (2 * Real.pi * ξ) ^ 2 * ε ^ 2 := by ring
        rw [this, h2]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith [sq_abs x, abs_nonneg x]
      rw [abs_le]
      constructor <;> nlinarith
  calc |∫ x, (ρ x * Real.cos (2 * Real.pi * x * ξ) - ρ x)|
      ≤ ∫ x, |ρ x * Real.cos (2 * Real.pi * x * ξ) - ρ x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, ρ x * ((2 * Real.pi * ε * ξ) ^ 2 / 2) :=
        integral_mono (hcos_int.sub hρi).abs (hρi.mul_const _) hpt
    _ = (2 * Real.pi * ε * ξ) ^ 2 / 2 := by
        rw [integral_mul_const, hρ, mollR_integral, one_mul]

end AEGIS.RHMollifyV1

#print axioms AEGIS.RHMollifyV1.fourier_moll_sub_one
