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

import FormalConjecturesUtil
import FormalConjectures.Other.CaratheodoryLoewnerCounterexample.Smooth
import Mathlib.Topology.Homotopy.Lifting

/-!
# Index of the announced Carathéodory–Loewner counterexamples

This file computes the winding number of the trace-free Hessian near the origin.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Metric
open Filter
open scoped ContDiff Topology unitInterval

namespace CaratheodoryLoewnerCounterexample

open LoewnerConjecture

@[category API, AMS 26]
private theorem traceFreeHessian_eq_zero_of_second_fderiv_eq_zero (f : ℂ → ℝ) (z : ℂ)
    (h : fderiv ℝ (fun w ↦ fderiv ℝ f w) z = 0) :
    traceFreeHessian f z = 0 := by
  simp [traceFreeHessian, h]

/-- The explicit trace-free Hessian of the seed. Keeping this local avoids adding another
public synonym for a one-line expression. -/
private noncomputable def seedTraceFreeHessianModel (z : ℂ) : ℂ :=
  ((Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
      1 / 2 * Real.cos (4 * z.im) : ℝ) : ℂ) +
    ((2 * Real.cos z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I

private noncomputable def seedGradient (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im) • Complex.reCLM +
    (-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im) • Complex.imCLM

private noncomputable def seedHessian (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((Real.cos (2 * z.re) - Real.sin z.re * Real.sin z.im) • Complex.reCLM +
      (Real.cos z.re * Real.cos z.im) • Complex.imCLM).smulRight Complex.reCLM +
    ((Real.cos z.re * Real.cos z.im) • Complex.reCLM +
      (-6 / 5 * Real.cos (2 * z.im) + 1 / 2 * Real.cos (4 * z.im) -
        Real.sin z.re * Real.sin z.im) • Complex.imCLM).smulRight Complex.imCLM

private noncomputable def seedWirtingerModel (z : ℂ) : ℂ :=
  (((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ) -
    ((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I) / 2

@[category API, AMS 26]
private theorem seedTraceFreeHessianModel_neg (z : ℂ) :
    seedTraceFreeHessianModel (-z) = seedTraceFreeHessianModel z := by
  simp [seedTraceFreeHessianModel]

@[category API, AMS 26]
private theorem seedWirtingerModel_neg (z : ℂ) :
    seedWirtingerModel (-z) = -seedWirtingerModel z := by
  simp [seedWirtingerModel]
  ring

@[category API, AMS 26]
private theorem seedWirtingerModel_eq_gradient (z : ℂ) :
    seedWirtingerModel z =
      ((seedGradient z 1 : ℂ) - (seedGradient z Complex.I : ℂ) * Complex.I) / 2 := by
  simp [seedWirtingerModel, seedGradient]

@[category API, AMS 26]
private theorem norm_seedWirtingerModel_le (z : ℂ) : ‖seedWirtingerModel z‖ ≤ 129 / 80 := by
  have hfx : |Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| ≤ 3 / 2 := by
    calc
      _ ≤ |Real.sin (2 * z.re) / 2| + |Real.cos z.re * Real.sin z.im| := abs_add_le ..
      _ = |Real.sin (2 * z.re)| / 2 + |Real.cos z.re| * |Real.sin z.im| := by
        rw [abs_div, abs_mul]
        norm_num
      _ ≤ 1 / 2 + 1 := by
        exact add_le_add
          (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num))
          (mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
      _ = 3 / 2 := by norm_num
  have hfy : |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im| ≤ 69 / 40 := by
    calc
      _ ≤ |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8| +
          |Real.sin z.re * Real.cos z.im| := abs_add_le ..
      _ ≤ |-3 * Real.sin (2 * z.im) / 5| + |Real.sin (4 * z.im) / 8| +
          |Real.sin z.re * Real.cos z.im| := by gcongr; exact abs_add_le ..
      _ = 3 / 5 * |Real.sin (2 * z.im)| + |Real.sin (4 * z.im)| / 8 +
          |Real.sin z.re| * |Real.cos z.im| := by
        rw [abs_div, abs_mul, abs_div, abs_mul]
        norm_num
        ring
      _ ≤ 3 / 5 + 1 / 8 + 1 := by
        exact add_le_add
          (add_le_add
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 3 / 5)))
            (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num)))
          (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg (Real.cos z.im))
            (Real.abs_cos_le_one _))
      _ = 69 / 40 := by norm_num
  calc
    ‖seedWirtingerModel z‖ ≤
        (|Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| +
          |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
            Real.sin z.re * Real.cos z.im|) / 2 := by
      have hmodel : seedWirtingerModel z =
          (((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ) -
            (((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I)) / 2 := rfl
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hmodel, norm_div, htwo]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        _ ≤ ‖((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ)‖ +
            ‖(((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ = |Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| +
            |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real]
          simp only [Complex.norm_I, mul_one, Real.norm_eq_abs]
    _ ≤ (3 / 2 + 69 / 40) / 2 := div_le_div_of_nonneg_right (add_le_add hfx hfy) (by norm_num)
    _ = 129 / 80 := by norm_num

/-- The seed has the uniform absolute-value bound used in the global Hessian estimates. -/
@[category API, AMS 26]
theorem counterexampleSeed_abs_le (z : ℂ) : |counterexampleSeed z| ≤ 253 / 160 := by
  calc
    _ ≤ |-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
          Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      simpa [counterexampleSeed] using abs_add_le
        (-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
          Real.cos (4 * z.im) / 32) (Real.sin z.re * Real.sin z.im)
    _ ≤ |-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10| +
          |Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      exact add_le_add (abs_sub (-Real.cos (2 * z.re) / 4 +
        3 * Real.cos (2 * z.im) / 10) (Real.cos (4 * z.im) / 32)) le_rfl
    _ ≤ |-Real.cos (2 * z.re) / 4| + |3 * Real.cos (2 * z.im) / 10| +
          |Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      exact add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = |Real.cos (2 * z.re)| / 4 + 3 / 10 * |Real.cos (2 * z.im)| +
          |Real.cos (4 * z.im)| / 32 + |Real.sin z.re| * |Real.sin z.im| := by
      rw [abs_div, abs_neg, abs_div, abs_mul, abs_div, abs_mul]
      norm_num
      ring
    _ ≤ 1 / 4 + 3 / 10 + 1 / 32 + 1 := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num))
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 3 / 10))))
          (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num)))
        (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg (Real.sin z.im))
          (Real.abs_sin_le_one _))
    _ = 253 / 160 := by norm_num

@[category API, AMS 26]
private theorem hasFDerivAt_counterexampleSeed (z : ℂ) :
    HasFDerivAt counterexampleSeed (seedGradient z) z := by
  let hx : HasFDerivAt (fun u : ℂ ↦ u.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  let hy : HasFDerivAt (fun u : ℂ ↦ u.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hraw := (((hx.const_mul 2).cos.neg.mul_const (4 : ℝ)⁻¹).add
    (((hy.const_mul 2).cos.const_mul 3).mul_const (10 : ℝ)⁻¹)).add
    (((hy.const_mul 4).cos.neg).mul_const (32 : ℝ)⁻¹) |>.add (hx.sin.mul hy.sin)
  convert hraw using 1
  · funext u
    simp [counterexampleSeed, sub_eq_add_neg, div_eq_mul_inv]
  · ext v
    simp [seedGradient]
    ring

@[category API, AMS 26]
private theorem hasFDerivAt_seedGradient (z : ℂ) :
    HasFDerivAt seedGradient (seedHessian z) z := by
  let hx : HasFDerivAt (fun u : ℂ ↦ u.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  let hy : HasFDerivAt (fun u : ℂ ↦ u.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hfx := ((hx.const_mul 2).sin.mul_const (2 : ℝ)⁻¹).add (hx.cos.mul hy.sin)
  have hfy := (((hy.const_mul 2).sin.const_mul (-3)).mul_const (5 : ℝ)⁻¹).add
    ((hy.const_mul 4).sin.mul_const (8 : ℝ)⁻¹) |>.add (hx.sin.mul hy.cos)
  have hraw := (hfx.smul_const Complex.reCLM).add (hfy.smul_const Complex.imCLM)
  let G : ℂ → (ℂ →L[ℝ] ℝ) :=
    (fun y ↦ (((fun y : ℂ ↦ Real.sin (2 * y.re) * (2 : ℝ)⁻¹) +
      (fun x : ℂ ↦ Real.cos x.re) * fun x : ℂ ↦ Real.sin x.im) y) • Complex.reCLM) +
    fun y ↦ ((((fun y : ℂ ↦ -3 * Real.sin (2 * y.im) * (5 : ℝ)⁻¹) +
      fun y : ℂ ↦ Real.sin (4 * y.im) * (8 : ℝ)⁻¹) +
      (fun x : ℂ ↦ Real.sin x.re) * fun x : ℂ ↦ Real.cos x.im) y) • Complex.imCLM
  have hfun : G = seedGradient := by
    funext u
    simp [G, seedGradient, div_eq_mul_inv]
  have hdiff : DifferentiableAt ℝ seedGradient z := by
    rw [← hfun]
    dsimp only [G]
    exact hraw.differentiableAt
  have hD : fderiv ℝ seedGradient z = seedHessian z := by
    rw [← hfun]
    dsimp only [G]
    rw [hraw.fderiv]
    apply DFunLike.coe_injective
    funext v
    apply DFunLike.coe_injective
    funext w
    simp [seedHessian]
    ring
  exact hdiff.hasFDerivAt.congr_fderiv hD

/-- Direct differentiation identifies the finite trigonometric Hessian model with the
repository's Fréchet-derivative encoding. -/
@[category API, AMS 26]
private theorem traceFreeHessian_counterexampleSeed (z : ℂ) :
    traceFreeHessian counterexampleSeed z = seedTraceFreeHessianModel z := by
  rw [traceFreeHessian]
  change (let H := fderiv ℝ (fun w ↦ fderiv ℝ counterexampleSeed w) z
    (H 1 1 - H Complex.I Complex.I : ℝ) + (2 * H 1 Complex.I : ℝ) * Complex.I) = _
  rw [show (fun w ↦ fderiv ℝ counterexampleSeed w) = seedGradient by
    funext w
    exact (hasFDerivAt_counterexampleSeed w).fderiv]
  rw [(hasFDerivAt_seedGradient z).fderiv]
  simp [seedHessian, seedTraceFreeHessianModel]
  ring

/-- The only part of the derivative of the seed's first Wirtinger derivative needed by the
anti-holomorphic chain rule. -/
@[category API, AMS 26]
private theorem exists_seedWirtingerModel_fderiv (z : ℂ) :
    ∃ Q : ℂ →L[ℝ] ℂ, HasFDerivAt seedWirtingerModel Q z ∧ ∀ b : ℂ,
      Q b + Complex.I * Q (-Complex.I * b) =
        b * star (seedTraceFreeHessianModel z) / 2 := by
  have hx := (hasFDerivAt_seedGradient z).clm_apply (hasFDerivAt_const (1 : ℂ) z)
  have hy := (hasFDerivAt_seedGradient z).clm_apply
    (hasFDerivAt_const Complex.I z)
  have hx' := Complex.ofRealCLM.hasFDerivAt.comp z hx
  have hy' := Complex.ofRealCLM.hasFDerivAt.comp z hy
  have hraw := (hx'.sub (hy'.mul_const Complex.I)).mul_const ((2 : ℂ)⁻¹)
  have heq : seedWirtingerModel = fun w ↦
      (((seedGradient w 1 : ℂ) - (seedGradient w Complex.I : ℂ) * Complex.I) / 2) := by
    funext w
    exact seedWirtingerModel_eq_gradient w
  let Q : ℂ →L[ℝ] ℂ := (2 : ℂ)⁻¹ •
    (Complex.ofRealCLM.comp ((seedHessian z).flip 1) -
      Complex.I • Complex.ofRealCLM.comp ((seedHessian z).flip Complex.I))
  have hqRaw : HasFDerivAt (fun w ↦
      (((seedGradient w 1 : ℂ) - (seedGradient w Complex.I : ℂ) * Complex.I) / 2)) Q z := by
    apply hraw.congr_fderiv
    ext b
    simp [Q]
  have hq : HasFDerivAt seedWirtingerModel Q z := by
    rw [heq]
    exact hqRaw
  refine ⟨Q, hq, fun b ↦ ?_⟩
  have hx2 : (2 : ℂ) * (z.re : ℂ) = ((2 * z.re : ℝ) : ℂ) := by
    push_cast
    ring
  have hy2 : (2 : ℂ) * (z.im : ℂ) = ((2 * z.im : ℝ) : ℂ) := by
    push_cast
    ring
  have hy4 : (4 : ℂ) * (z.im : ℂ) = ((4 * z.im : ℝ) : ℂ) := by
    push_cast
    ring
  apply Complex.ext
  · simp [Q, seedHessian, seedTraceFreeHessianModel, Complex.mul_re, Complex.mul_im]
    rw [hx2, hy2, hy4]
    simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    ring
  · simp [Q, seedHessian, seedTraceFreeHessianModel, Complex.mul_re, Complex.mul_im]
    rw [hx2, hy2, hy4]
    simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    ring

/-- The exact uniform nonvanishing certificate behind the index computation. -/
@[category API, AMS 26]
private theorem seven_div_fifty_le_norm_seedTraceFreeHessianModel (z : ℂ) :
    7 / 50 ≤ ‖seedTraceFreeHessianModel z‖ := by
  let s := Real.cos z.re ^ 2
  let t := Real.cos z.im ^ 2
  let a := -4 * t ^ 2 + 32 / 5 * t - 27 / 10
  let sstar := (4 * t ^ 2 - 37 / 5 * t + 27 / 10) / 2
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hs1 : s ≤ 1 := by
    have hplus : 0 ≤ 1 + Real.cos z.re := by linarith [Real.neg_one_le_cos z.re]
    have h := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z.re))
      hplus
    dsimp [s]
    nlinarith only [h]
  have ht1 : t ≤ 1 := by
    have hplus : 0 ≤ 1 + Real.cos z.im := by linarith [Real.neg_one_le_cos z.im]
    have h := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z.im))
      hplus
    dsimp [t]
    nlinarith only [h]
  have hcos4y : Real.cos (4 * z.im) =
      8 * Real.cos z.im ^ 4 - 8 * Real.cos z.im ^ 2 + 1 := by
    rw [show 4 * z.im = 2 * (2 * z.im) by ring, Real.cos_two_mul, Real.cos_two_mul]
    ring
  have hnorm : ‖seedTraceFreeHessianModel z‖ ^ 2 = (2 * s + a) ^ 2 + 4 * s * t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [seedTraceFreeHessianModel]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, add_zero, mul_one]
    have hreSq (x : ℝ) : x * x = x ^ 2 := by ring
    rw [hreSq, show (0 + 2 * Real.cos z.re * Real.cos z.im) *
        (0 + 2 * Real.cos z.re * Real.cos z.im) =
          (2 * Real.cos z.re * Real.cos z.im) ^ 2 by ring]
    rw [Real.cos_two_mul, Real.cos_two_mul, hcos4y]
    dsimp [s, t, a]
    ring
  have hcomplete : (2 * s + a) ^ 2 + 4 * s * t =
      4 * (s - sstar) ^ 2 + t * (8 * t ^ 2 - 69 / 5 * t + 27 / 5) := by
    dsimp [a, sstar]
    ring
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hnorm]
  by_cases htlow : t ≤ 1 / 10
  · have hfactor : 0 ≤ (t - 1 / 10) * (4 * t - 7) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hstar : 1 ≤ sstar := by
      dsimp [sstar]
      nlinarith only [ht0, htlow, sq_nonneg t]
    have hdist : (1 - sstar) ^ 2 ≤ (s - sstar) ^ 2 := by
      have hprod : 0 ≤ (s - 1) * (s + 1 - 2 * sstar) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith only [hprod]
    have hP1 : (2 + a) ^ 2 + 4 * t ≤ (2 * s + a) ^ 2 + 4 * s * t := by
      dsimp [a, sstar] at hdist ⊢
      nlinarith only [hdist]
    by_cases ht64 : 1 / 64 ≤ t
    · nlinarith only [hP1, ht64, sq_nonneg (2 + a)]
    · have hA : 2 + a ≤ -3 / 5 := by
        dsimp [a]
        nlinarith only [ht0, ht64, sq_nonneg t]
      have hneg : 0 ≤ -(2 + a) := by linarith only [hA]
      have hsq : (7 / 50) ^ 2 ≤ (2 + a) ^ 2 := by
        rw [show (2 + a) ^ 2 = (-(2 + a)) ^ 2 by ring]
        exact (sq_le_sq₀ (by norm_num) hneg).2 (by linarith only [hA])
      nlinarith only [hP1, hsq, ht0]
  · have htlo : 1 / 10 ≤ t := by linarith only [htlow]
    by_cases htmid : t ≤ 1 / 2
    · have hquad : 8 * t ^ 2 - 49 / 5 * t + 1 / 2 ≤ 0 := by
        have hfactor : (t - 1 / 10) * (8 * (t + 1 / 10) - 49 / 5) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        nlinarith only [hfactor]
      have hfactor : 0 ≤
          (t - 1 / 2) * (8 * t ^ 2 - 49 / 5 * t + 1 / 2) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hquad
      have hminimum : 1 / 4 ≤ t * (8 * t ^ 2 - 69 / 5 * t + 27 / 5) := by
        nlinarith only [hfactor]
      rw [hcomplete]
      nlinarith only [hminimum, sq_nonneg (s - sstar)]
    · have hthi : 1 / 2 ≤ t := by linarith only [htmid]
      have hfactor : (t - 1 / 2) * (4 * (t + 1 / 2) - 37 / 5) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hstar : sstar ≤ 0 := by
        dsimp [sstar]
        nlinarith only [hfactor]
      have hdist : (-sstar) ^ 2 ≤ (s - sstar) ^ 2 := by
        have hprod : 0 ≤ s * (s - 2 * sstar) := mul_nonneg hs0 (by linarith)
        nlinarith only [hprod]
      have hP0 : a ^ 2 ≤ (2 * s + a) ^ 2 + 4 * s * t := by
        dsimp [a, sstar] at hdist ⊢
        nlinarith only [hdist]
      have hA : a ≤ -7 / 50 := by
        dsimp [a]
        nlinarith only [hthi, ht1, sq_nonneg (t - 4 / 5)]
      have hneg : 0 ≤ -a := by linarith only [hA]
      have hsq : (7 / 50) ^ 2 ≤ a ^ 2 := by
        rw [show a ^ 2 = (-a) ^ 2 by ring]
        exact (sq_le_sq₀ (by norm_num) hneg).2 (by linarith only [hA])
      nlinarith only [hP0, hsq]

/-- The trace-free Hessian of the seed is uniformly separated from zero. -/
@[category API, AMS 26]
theorem counterexampleSeed_traceFreeHessian_norm_lower (z : ℂ) :
    7 / 50 ≤ ‖traceFreeHessian counterexampleSeed z‖ := by
  rw [traceFreeHessian_counterexampleSeed]
  exact seven_div_fifty_le_norm_seedTraceFreeHessianModel z

/-- A deliberately crude uniform upper bound for the seed's trace-free Hessian. -/
@[category API, AMS 26]
theorem counterexampleSeed_traceFreeHessian_norm_upper (z : ℂ) :
    ‖traceFreeHessian counterexampleSeed z‖ ≤ 47 / 10 := by
  rw [traceFreeHessian_counterexampleSeed]
  have hre : |Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
      1 / 2 * Real.cos (4 * z.im)| ≤ 1 + 6 / 5 + 1 / 2 := by
    calc
      _ ≤ |Real.cos (2 * z.re)| + |6 / 5 * Real.cos (2 * z.im)| +
          |1 / 2 * Real.cos (4 * z.im)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |Real.cos (2 * z.re)| + 6 / 5 * |Real.cos (2 * z.im)| +
          1 / 2 * |Real.cos (4 * z.im)| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 1 + 6 / 5 + 1 / 2 := by
        exact add_le_add
          (add_le_add (Real.abs_cos_le_one _)
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 6 / 5))))
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (4 * z.im))
              (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  have him : |2 * Real.cos z.re * Real.cos z.im| ≤ 2 := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |Real.cos z.re| * |Real.cos z.im| ≤ 2 * 1 * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
            (by norm_num : (0 : ℝ) ≤ 2))
          (Real.abs_cos_le_one _) (abs_nonneg (Real.cos z.im))
          (by norm_num)
      _ = 2 := by norm_num
  calc
    ‖seedTraceFreeHessianModel z‖ ≤
        |Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
          1 / 2 * Real.cos (4 * z.im)| +
        |2 * Real.cos z.re * Real.cos z.im| := by
      rw [seedTraceFreeHessianModel]
      calc
        _ ≤ ‖((Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
              1 / 2 * Real.cos (4 * z.im) : ℝ) : ℂ)‖ +
            ‖((2 * Real.cos z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I‖ :=
          norm_add_le _ _
        _ = _ := by rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I,
          mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 + 6 / 5 + 1 / 2) + 2 := add_le_add hre him
    _ = 47 / 10 := by norm_num

/-- The scalar trace of the seed Hessian has a uniform absolute-value bound. -/
@[category API, AMS 26]
theorem counterexampleSeed_chartLaplacian_abs_le (z : ℂ) :
    |let H := fderiv ℝ (fun w ↦ fderiv ℝ counterexampleSeed w) z;
      H 1 1 + H Complex.I Complex.I| ≤ 47 / 10 := by
  rw [show (fun w ↦ fderiv ℝ counterexampleSeed w) = seedGradient by
    funext w
    exact (hasFDerivAt_counterexampleSeed w).fderiv]
  rw [(hasFDerivAt_seedGradient z).fderiv]
  have hformula : seedHessian z 1 1 + seedHessian z Complex.I Complex.I =
      Real.cos (2 * z.re) - 6 / 5 * Real.cos (2 * z.im) +
        1 / 2 * Real.cos (4 * z.im) - 2 * Real.sin z.re * Real.sin z.im := by
    simp [seedHessian]
    ring
  rw [hformula]
  have htriangle :
      |Real.cos (2 * z.re) - 6 / 5 * Real.cos (2 * z.im) +
          1 / 2 * Real.cos (4 * z.im) - 2 * Real.sin z.re * Real.sin z.im| ≤
        |Real.cos (2 * z.re)| + |-6 / 5 * Real.cos (2 * z.im)| +
          |1 / 2 * Real.cos (4 * z.im)| + |-2 * Real.sin z.re * Real.sin z.im| := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    rw [show -(6 / 5 * Real.cos (2 * z.im)) =
        -6 / 5 * Real.cos (2 * z.im) by ring,
      show -(2 * Real.sin z.re * Real.sin z.im) =
        -2 * Real.sin z.re * Real.sin z.im by ring]
    calc
      _ ≤ |Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im) +
            1 / 2 * Real.cos (4 * z.im)| +
          |-2 * Real.sin z.re * Real.sin z.im| := abs_add_le ..
      _ ≤ (|Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im)| +
            |1 / 2 * Real.cos (4 * z.im)|) +
          |-2 * Real.sin z.re * Real.sin z.im| := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (abs_add_le
              (Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im))
              (1 / 2 * Real.cos (4 * z.im)))
            |-2 * Real.sin z.re * Real.sin z.im|
      _ ≤ ((|Real.cos (2 * z.re)| + |-6 / 5 * Real.cos (2 * z.im)|) +
            |1 / 2 * Real.cos (4 * z.im)|) +
          |-2 * Real.sin z.re * Real.sin z.im| := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (add_le_add_right
              (abs_add_le (Real.cos (2 * z.re))
                (-6 / 5 * Real.cos (2 * z.im)))
              |1 / 2 * Real.cos (4 * z.im)|)
            |-2 * Real.sin z.re * Real.sin z.im|
  refine htriangle.trans ?_
  simp only [abs_mul]
  norm_num
  have hsin : |Real.sin z.re| * |Real.sin z.im| ≤ 1 :=
    mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _)
  nlinarith only [Real.abs_cos_le_one (2 * z.re),
    Real.abs_cos_le_one (2 * z.im), Real.abs_cos_le_one (4 * z.im), hsin]

/-- The first Wirtinger derivative of the seed has a uniform norm bound. -/
@[category API, AMS 26]
theorem counterexampleSeed_wirtinger_norm_upper (z : ℂ) :
    ‖((fderiv ℝ counterexampleSeed z 1 : ℂ) -
        (fderiv ℝ counterexampleSeed z Complex.I : ℂ) * Complex.I) / 2‖ ≤ 129 / 80 := by
  rw [(hasFDerivAt_counterexampleSeed z).fderiv]
  rw [← seedWirtingerModel_eq_gradient]
  exact norm_seedWirtingerModel_le z

/-- The normalized seed Hessian has a global continuous argument, chosen evenly under
`z ↦ -z`. This is what makes the half-integral powers for odd `k` contribute no extra winding. -/
@[category API, AMS 26]
private theorem exists_even_continuous_seed_argument :
    ∃ θ : ℂ → ℝ, Continuous θ ∧
      (∀ z, Complex.exp ((θ z : ℂ) * Complex.I) =
        seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖) ∧
      ∀ z, θ (-z) = θ z := by
  have hmodel0 (z : ℂ) : seedTraceFreeHessianModel z ≠ 0 := by
    rw [← norm_pos_iff]
    exact (by norm_num : (0 : ℝ) < 7 / 50).trans_le
      (seven_div_fifty_le_norm_seedTraceFreeHessianModel z)
  have hmodel_cont : Continuous seedTraceFreeHessianModel := by
    unfold seedTraceFreeHessianModel
    fun_prop
  have hmodel_even := seedTraceFreeHessianModel_neg
  let qCircle : C(ℂ, Circle) :=
    ⟨fun z ↦ ⟨seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div]
        simp [hmodel0 z]⟩,
      (hmodel_cont.div (Complex.continuous_ofReal.comp hmodel_cont.norm)
        (fun z ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hmodel0 z)))).subtype_mk _⟩
  let θ0 := Complex.arg (qCircle 0 : ℂ)
  rcases Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts qCircle 0 θ0
      (Circle.exp_arg (qCircle 0)) with ⟨θ, ⟨-, hθ⟩, -⟩
  have hθ' (z : ℂ) : Circle.exp (θ z) = qCircle z := congrFun hθ z
  have hθeven : (fun z : ℂ ↦ θ (-z)) = θ := by
    refine Circle.isCoveringMap_exp.eq_of_comp_eq
      (θ.continuous.comp continuous_neg) θ.continuous ?_ (0 : ℂ) ?_
    · funext z
      simp only [Function.comp_apply]
      rw [hθ', hθ']
      apply Subtype.ext
      simp [qCircle, hmodel_even]
    · simp
  refine ⟨θ, θ.continuous, ?_, fun z ↦ congrFun hθeven z⟩
  intro z
  have hz := congrArg (fun w : Circle ↦ (w : ℂ)) (hθ' z)
  simpa [qCircle] using hz

/-- The lifted leading Hessian model on a circle has argument change `2π(2+k)`. The path in
the seed variable is chosen continuously, rather than by the discontinuous principal branch. -/
@[category API, AMS 26]
private theorem exists_seed_leading_argument (k : ℕ) (a c : ℝ) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        Complex.exp (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) *
          star (seedTraceFreeHessianModel
            ((a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I))) /
          ‖seedTraceFreeHessianModel
            ((a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I))‖) ∧
      θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  rcases exists_even_continuous_seed_argument with ⟨φ, hφcont, hφ, hφeven⟩
  let w : ℝ → ℂ := fun t ↦
    (a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I)
  let θ : ℝ → ℝ := fun t ↦ c + (2 + k : ℕ) * t - φ (w t)
  have hwcont : Continuous w := by
    fun_prop
  have hθcont : Continuous θ := by
    fun_prop
  have hphase (t : ℝ) : Complex.exp ((θ t : ℂ) * Complex.I) =
      Complex.exp (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) *
        star (seedTraceFreeHessianModel (w t)) / ‖seedTraceFreeHessianModel (w t)‖ := by
    have hs := congrArg star (hφ (w t))
    rw [show ((θ t : ℂ) * Complex.I) =
      (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) +
        -((φ (w t) : ℂ) * Complex.I) by simp [θ]; ring, Complex.exp_add]
    have hs' : Complex.exp (-((φ (w t) : ℂ) * Complex.I)) =
        star (seedTraceFreeHessianModel (w t)) /
          ‖seedTraceFreeHessianModel (w t)‖ := by
      calc
        _ = star (Complex.exp ((φ (w t) : ℂ) * Complex.I)) := by
          change Complex.exp (-((φ (w t) : ℂ) * Complex.I)) =
            (starRingEnd ℂ) (Complex.exp ((φ (w t) : ℂ) * Complex.I))
          rw [← Complex.exp_conj]
          congr 1
          simp
        _ = star (seedTraceFreeHessianModel (w t) /
            ‖seedTraceFreeHessianModel (w t)‖) := hs
        _ = _ := by simp
    rw [hs']
    ring
  have hexp : Complex.exp ((((k : ℝ) * Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ k := by
    rw [show (((k : ℝ) * Real.pi : ℂ) * Complex.I) =
      (k : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hwendpoint : φ (w (2 * Real.pi)) = φ (w 0) := by
    have hwvalue : w (2 * Real.pi) = (a : ℂ) * (-1 : ℂ) ^ k := by
      simp only [w]
      rw [show k / 2 * (2 * Real.pi) = (k : ℝ) * Real.pi by ring]
      congr 1
      simpa only [Complex.ofReal_mul] using hexp
    rcases neg_one_pow_eq_or ℂ k with hk | hk
    · rw [hwvalue, hk]
      simp [w]
    · rw [hwvalue, hk]
      simpa [w] using hφeven (a : ℂ)
  refine ⟨θ, hθcont, fun t ↦ by simpa [w] using hphase t, ?_⟩
  dsimp [θ]
  rw [hwendpoint]
  have hcast : ((2 + k : ℕ) : ℝ) = ((2 + (k : ℤ) : ℤ) : ℝ) := by
    norm_num
  rw [hcast]
  ring

/-- Lifting a homotopy through the exponential covering preserves the total argument change
when every stage has matching endpoints. -/
@[category API, AMS 26]
private theorem homotopy_preserves_argument_change (H : C(I × ℝ, Circle))
    (θ0 : C(ℝ, ℝ)) (T C : ℝ) (hH0 : ∀ t, H (0, t) = Circle.exp (θ0 t))
    (hperiodic : ∀ s, H (s, T) = H (s, 0)) (hchange : θ0 T - θ0 0 = C)
    (hC : Circle.exp C = 1) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, Circle.exp (θ t) = H (1, t)) ∧
      θ T - θ 0 = C := by
  let Θ := Circle.isCoveringMap_exp.liftHomotopy H θ0 hH0
  have hΘ (s : I) (t : ℝ) : Circle.exp (Θ (s, t)) = H (s, t) := by
    exact congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H θ0 hH0) (s, t)
  have hendpoint : (fun s : I ↦ Θ (s, T)) = fun s ↦ Θ (s, 0) + C := by
    refine Circle.isCoveringMap_exp.eq_of_comp_eq
      (Θ.continuous.comp (continuous_id.prodMk continuous_const))
      ((Θ.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const)
      ?_ (0 : I) ?_
    · funext s
      simp only [Function.comp_apply]
      rw [Circle.exp_add, hC, mul_one, hΘ, hΘ, hperiodic]
    · change Θ (0, T) = Θ (0, 0) + C
      rw [Circle.isCoveringMap_exp.liftHomotopy_zero,
        Circle.isCoveringMap_exp.liftHomotopy_zero]
      linarith
  refine ⟨fun t ↦ Θ (1, t),
    Θ.continuous.comp (continuous_const.prodMk continuous_id), fun t ↦ hΘ 1 t, ?_⟩
  have := congrFun hendpoint 1
  change Θ (1, T) = Θ (1, 0) + C at this
  linarith

/-- A positive real power of the radius tends to zero on the punctured complex plane. -/
@[category API, AMS 26]
private theorem tendsto_norm_rpow_nhdsWithin_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ p) (𝓝[≠] 0) (𝓝 0) := by
  have hrpow := (Real.continuousAt_rpow_const 0 p (.inr hp.le)).tendsto
  have hnormAt : ContinuousAt (fun z : ℂ ↦ ‖z‖) 0 := continuous_norm.continuousAt
  have hnorm : Tendsto (fun z : ℂ ↦ ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hnormAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  simpa only [Function.comp_apply, Real.zero_rpow hp.ne'] using hrpow.comp hnorm

/-- The three powers occurring in the Hessian error-to-leading ratios all tend to zero for
positive `k`. -/
@[category API, AMS 26]
private theorem counterexample_error_powers_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) / 2)) (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4)) (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) - 1 / 2)) (𝓝[≠] 0) (𝓝 0) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨tendsto_norm_rpow_nhdsWithin_zero (by positivity),
    tendsto_norm_rpow_nhdsWithin_zero (by linarith),
    tendsto_norm_rpow_nhdsWithin_zero (by linarith)⟩

/-- A perturbation smaller in norm than a nonvanishing leading term has the same argument
change. The proof uses the normalized straight-line homotopy. -/
@[category API, AMS 26]
private theorem exists_argument_of_norm_error_lt (leading error : ℝ → ℂ) (T C : ℝ)
    (hleading : Continuous leading) (herror : Continuous error)
    (hsmall : ∀ t, ‖error t‖ < ‖leading t‖)
    (hperiodicLeading : leading T = leading 0) (hperiodicError : error T = error 0)
    (θ0 : ℝ → ℝ) (hθ0 : Continuous θ0)
    (hphase0 : ∀ t, Complex.exp ((θ0 t : ℂ) * Complex.I) = leading t / ‖leading t‖)
    (hchange : θ0 T - θ0 0 = C) (hC : Circle.exp C = 1) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (leading t + error t) / ‖leading t + error t‖) ∧
      θ T - θ 0 = C := by
  have hne (s : I) (t : ℝ) : leading t + (s : ℝ) • error t ≠ 0 := by
    intro hzero
    have heq : leading t = -((s : ℝ) • error t) := eq_neg_of_add_eq_zero_left hzero
    have hle : ‖leading t‖ ≤ ‖error t‖ := by
      rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg s.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.2.2
    exact (not_lt_of_ge hle) (hsmall t)
  have hscalar : Continuous (fun st : I × ℝ ↦ (st.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have herror' : Continuous (fun st : I × ℝ ↦ error st.2) :=
    herror.comp continuous_snd
  have htotal : Continuous (fun st : I × ℝ ↦
      leading st.2 + (st.1 : ℝ) • error st.2) :=
    (hleading.comp continuous_snd).add (hscalar.smul herror')
  let H : C(I × ℝ, Circle) :=
    ⟨fun st ↦ ⟨(leading st.2 + (st.1 : ℝ) • error st.2) /
          ‖leading st.2 + (st.1 : ℝ) • error st.2‖, mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact div_self (norm_ne_zero_iff.mpr (hne st.1 st.2))⟩,
      (htotal.div
          (Complex.continuous_ofReal.comp htotal.norm)
          (fun st ↦ Complex.ofReal_ne_zero.mpr
            (norm_ne_zero_iff.mpr (hne st.1 st.2)))).subtype_mk _⟩
  let θ0Map : C(ℝ, ℝ) := ⟨θ0, hθ0⟩
  have hH0 (t : ℝ) : H (0, t) = Circle.exp (θ0Map t) := by
    apply Subtype.ext
    simpa [H, θ0Map] using (hphase0 t).symm
  have hHperiodic (s : I) : H (s, T) = H (s, 0) := by
    apply Subtype.ext
    simp [H, hperiodicLeading, hperiodicError]
  rcases homotopy_preserves_argument_change H θ0Map T C hH0 hHperiodic hchange hC with
    ⟨θ, hθ, hphase, hθchange⟩
  refine ⟨θ, hθ, ?_, hθchange⟩
  intro t
  have ht := congrArg (fun w : Circle ↦ (w : ℂ)) (hphase t)
  simpa [H] using ht

/-- The radial amplitude in the counterexample, separated from the oscillatory seed. -/
private noncomputable def counterexampleRadialAmplitude (r : ℝ) : ℝ :=
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) /
    (1 + r ^ 2)

/-- The logarithmic derivative of the radial amplitude on the positive real axis. -/
private noncomputable def counterexampleRadialLogDerivOne (r : ℝ) : ℝ :=
  2 / r - 2 * r / (1 + r ^ 2) + Real.exp (-(r ^ 2)) *
    (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))

/-- The derivative of `counterexampleRadialLogDerivOne` on the positive real axis. -/
private noncomputable def counterexampleRadialLogDerivTwo (r : ℝ) : ℝ :=
  -2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2 + Real.exp (-(r ^ 2)) *
    (Real.rpow r (-(1 : ℝ) / 4) - 5 / 16 * Real.rpow r (-(9 : ℝ) / 4) -
      4 * Real.rpow r (7 / 4))

/-- Crude radial logarithmic-derivative bounds, sufficient for the Hessian error estimate. -/
@[category API, AMS 26]
private theorem counterexampleRadialLogDeriv_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |counterexampleRadialLogDerivOne r| ≤ 7 * r ^ (-(5 : ℝ) / 4) ∧
      |counterexampleRadialLogDerivTwo r| ≤ 10 * r ^ (-(9 : ℝ) / 4) := by
  have hexp0 : 0 ≤ Real.exp (-(r ^ 2)) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-(r ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg r))
  have hpFive : 0 < r ^ (-(5 : ℝ) / 4) := Real.rpow_pos_of_pos hr _
  have hpNine : 0 < r ^ (-(9 : ℝ) / 4) := Real.rpow_pos_of_pos hr _
  have hFiveOne : 1 ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
  have hNineOne : 1 ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
  have hNegOneFive : r ^ (-(1 : ℝ)) ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hNegTwoNine : r ^ (-(2 : ℝ)) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hThreeFive : r ^ ((3 : ℝ) / 4) ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hOneNine : r ^ (-(1 : ℝ) / 4) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hSevenNine : r ^ ((7 : ℝ) / 4) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hfirst : |2 / r| ≤ 2 * r ^ (-(5 : ℝ) / 4) := by
    rw [abs_div, abs_of_nonneg (by norm_num), abs_of_pos hr]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    gcongr
  have hsecond : |2 * r / (1 + r ^ 2)| ≤ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num), abs_of_pos hr,
      abs_of_pos (by positivity : 0 < 1 + r ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ 2)).2
    nlinarith
  have hexpTerm : Real.exp (-(r ^ 2)) *
      (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4)) ≤
      9 / 4 * r ^ (-(5 : ℝ) / 4) := by
    calc
      _ ≤ 1 * (1 / 4 * r ^ (-(5 : ℝ) / 4) +
          2 * r ^ ((3 : ℝ) / 4)) := by gcongr
      _ ≤ _ := by nlinarith only [hThreeFive, hpFive]
  constructor
  · rw [counterexampleRadialLogDerivOne]
    calc
      |2 / r - 2 * r / (1 + r ^ 2) + Real.exp (-(r ^ 2)) *
          (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4))| ≤
          |2 / r| + |2 * r / (1 + r ^ 2)| +
            |Real.exp (-(r ^ 2)) *
              (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4))| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 2 * r ^ (-(5 : ℝ) / 4) + 2 +
          9 / 4 * r ^ (-(5 : ℝ) / 4) := by
        gcongr
        rw [abs_of_nonneg (mul_nonneg hexp0 (by positivity))]
        exact hexpTerm
      _ ≤ 7 * r ^ (-(5 : ℝ) / 4) := by nlinarith only [hFiveOne]
  · have hmiddle : |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| ≤ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_pos (by positivity : 0 < (1 + r ^ 2) ^ 2)]
      have hrsq : r ^ 2 ≤ 1 := by nlinarith
      have habs : |r ^ 2 - 1| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
      apply (div_le_iff₀ (by positivity : 0 < (1 + r ^ 2) ^ 2)).2
      nlinarith [sq_nonneg (r ^ 2)]
    have hexpTermTwo : |Real.exp (-(r ^ 2)) *
        (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
          4 * r ^ ((7 : ℝ) / 4))| ≤ 85 / 16 * r ^ (-(9 : ℝ) / 4) := by
      rw [abs_mul, abs_of_nonneg hexp0]
      have hinside :
          |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4)| ≤
            r ^ (-(1 : ℝ) / 4) + 5 / 16 * r ^ (-(9 : ℝ) / 4) +
              4 * r ^ ((7 : ℝ) / 4) := by
        calc
          _ ≤ |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4)| +
              |4 * r ^ ((7 : ℝ) / 4)| := abs_sub ..
          _ ≤ |r ^ (-(1 : ℝ) / 4)| + |5 / 16 * r ^ (-(9 : ℝ) / 4)| +
              |4 * r ^ ((7 : ℝ) / 4)| := add_le_add (abs_sub _ _) le_rfl
          _ = _ := by
            rw [abs_mul, abs_mul, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg,
              abs_of_nonneg, abs_of_nonneg]
            all_goals positivity
      calc
        Real.exp (-(r ^ 2)) *
            |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4)| ≤
            1 * (r ^ (-(1 : ℝ) / 4) + 5 / 16 * r ^ (-(9 : ℝ) / 4) +
              4 * r ^ ((7 : ℝ) / 4)) := by gcongr
        _ ≤ _ := by nlinarith only [hOneNine, hSevenNine, hpNine]
    rw [counterexampleRadialLogDerivTwo]
    calc
      |-2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2 +
          Real.exp (-(r ^ 2)) *
            (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4))| ≤
          |2 / r ^ 2| + |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| +
            |Real.exp (-(r ^ 2)) *
              (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                4 * r ^ ((7 : ℝ) / 4))| := by
        calc
          _ ≤ |-2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| +
              |Real.exp (-(r ^ 2)) *
                (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                  4 * r ^ ((7 : ℝ) / 4))| := abs_add_le ..
          _ ≤ (|-2 / r ^ 2| + |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2|) +
              |Real.exp (-(r ^ 2)) *
                (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                  4 * r ^ ((7 : ℝ) / 4))| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by
            rw [show -2 / r ^ 2 = -(2 / r ^ 2) by ring, abs_neg]
      _ ≤ 2 * r ^ (-(9 : ℝ) / 4) + 2 +
          85 / 16 * r ^ (-(9 : ℝ) / 4) := by
        gcongr
        have hinv : (r ^ 2)⁻¹ = r ^ (-(2 : ℝ)) := by
          calc
            (r ^ 2)⁻¹ = (r ^ (2 : ℝ))⁻¹ :=
              congrArg Inv.inv (Real.rpow_natCast r 2).symm
            _ = r ^ (-(2 : ℝ)) := (Real.rpow_neg hr.le (2 : ℝ)).symm
        rw [abs_div, abs_of_nonneg (by norm_num), abs_of_pos (sq_pos_of_pos hr),
          div_eq_mul_inv, hinv]
        exact mul_le_mul_of_nonneg_left hNegTwoNine (by norm_num)
      _ ≤ 10 * r ^ (-(9 : ℝ) / 4) := by nlinarith only [hNineOne]

@[category API, AMS 26]
private theorem hasDerivAt_counterexampleRadialExponent {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun x : ℝ ↦ -Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2)))
      (Real.exp (-(r ^ 2)) *
        (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))) r := by
  have hpow :=
    (Real.hasDerivAt_rpow_const (x := r) (p := -(1 : ℝ) / 4) (Or.inl hr.ne')).neg
  have hexp := ((hasDerivAt_id r).pow 2).neg.exp
  have hpow' : HasDerivAt (fun x : ℝ ↦ -Real.rpow x (-(1 : ℝ) / 4))
      (1 / 4 * Real.rpow r (-(5 : ℝ) / 4)) r := by
    convert hpow using 1
    simp only [Real.rpow_eq_pow]
    rw [show -(1 : ℝ) / 4 - 1 = -5 / 4 by ring]
    ring
  have hexp' : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2)))
      (-2 * r * Real.exp (-(r ^ 2))) r := by
    convert hexp using 1
    simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
    ring
  have hrpow : r * Real.rpow r (-(1 : ℝ) / 4) = Real.rpow r (3 / 4) := by
    calc
      r * Real.rpow r (-(1 : ℝ) / 4) =
          Real.rpow r 1 * Real.rpow r (-(1 : ℝ) / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (-(1 : ℝ) / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + (-(1 : ℝ) / 4)) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (3 / 4) := by
        congr 1
        ring
  convert hpow'.mul hexp' using 1
  calc
    Real.exp (-(r ^ 2)) *
          (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4)) =
        1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          2 * Real.rpow r (3 / 4) * Real.exp (-(r ^ 2)) := by ring
    _ = 1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          2 * (r * Real.rpow r (-(1 : ℝ) / 4)) * Real.exp (-(r ^ 2)) := by rw [hrpow]
    _ = 1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          -Real.rpow r (-(1 : ℝ) / 4) * (-2 * r * Real.exp (-(r ^ 2))) := by ring

@[category API, AMS 26]
private theorem hasDerivAt_counterexampleRadialAmplitude {r : ℝ} (hr : 0 < r) :
    HasDerivAt counterexampleRadialAmplitude
      (counterexampleRadialAmplitude r * counterexampleRadialLogDerivOne r) r := by
  have hE := (hasDerivAt_counterexampleRadialExponent hr).exp
  have hnum := ((hasDerivAt_id r).pow 2).mul hE
  have hden := (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)
  have hnum' : HasDerivAt (fun x : ℝ ↦ x ^ 2 *
      Real.exp (-Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2))))
      (2 * r * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) +
        r ^ 2 * (Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
          (Real.exp (-(r ^ 2)) *
            (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))))) r := by
    simpa [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, id_eq] using hnum
  have hden' : HasDerivAt (fun x : ℝ ↦ 1 + x ^ 2) (2 * r) r := by
    convert hden using 1
    norm_num [Pi.add_apply, Pi.pow_apply, id_eq]
  convert hnum'.div hden' (by positivity) using 1
  simp only [counterexampleRadialAmplitude, counterexampleRadialLogDerivOne]
  field_simp [hr.ne']
  ring

@[category API, AMS 26]
private theorem hasDerivAt_counterexampleRadialLogDerivOne {r : ℝ} (hr : 0 < r) :
    HasDerivAt counterexampleRadialLogDerivOne (counterexampleRadialLogDerivTwo r) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hfirst := (hasDerivAt_const r 2).div (hasDerivAt_id r) hr0
  have hmiddle := ((hasDerivAt_const r 2).mul (hasDerivAt_id r)).div
    ((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)) (by dsimp; positivity)
  have hexp := ((hasDerivAt_id r).pow 2).neg.exp
  have hpFive := Real.hasDerivAt_rpow_const (x := r) (p := -(5 : ℝ) / 4) (Or.inl hr0)
  have hpThree := Real.hasDerivAt_rpow_const (x := r) (p := (3 : ℝ) / 4) (Or.inl hr0)
  have hlast := hexp.mul
    ((hasDerivAt_const r (1 / 4)).mul hpFive |>.add
      ((hasDerivAt_const r 2).mul hpThree))
  have hseven : r * Real.rpow r (3 / 4) = Real.rpow r (7 / 4) := by
    calc
      r * Real.rpow r (3 / 4) = Real.rpow r 1 * Real.rpow r (3 / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (3 / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + 3 / 4) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (7 / 4) := by
        congr 1
        ring
  have hminus : r * Real.rpow r (-(5 : ℝ) / 4) = Real.rpow r (-(1 : ℝ) / 4) := by
    calc
      r * Real.rpow r (-(5 : ℝ) / 4) =
          Real.rpow r 1 * Real.rpow r (-(5 : ℝ) / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (-(5 : ℝ) / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + (-(5 : ℝ) / 4)) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (-(1 : ℝ) / 4) := by
        congr 1
        ring
  have hfirst' : HasDerivAt (fun x : ℝ ↦ 2 / x) (-2 / r ^ 2) r := by
    convert hfirst using 1
    simp only [id_eq, zero_mul]
    field_simp [hr0]
    ring
  have hmiddle' : HasDerivAt (fun x : ℝ ↦ 2 * x / (1 + x ^ 2))
      (2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) r := by
    convert hmiddle using 1
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, zero_mul, zero_add]
    field_simp
    ring
  have hlast' : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2)) *
      (1 / 4 * Real.rpow x (-(5 : ℝ) / 4) + 2 * Real.rpow x (3 / 4)))
      (Real.exp (-(r ^ 2)) *
        (Real.rpow r (-(1 : ℝ) / 4) - 5 / 16 * Real.rpow r (-(9 : ℝ) / 4) -
          4 * Real.rpow r (7 / 4))) r := by
    convert hlast using 1
    simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, zero_mul, zero_add, Real.rpow_eq_pow]
    norm_num only [Nat.reduceSub, pow_one, mul_one, one_mul]
    have hseven' : r * r ^ ((3 : ℝ) / 4) = r ^ ((7 : ℝ) / 4) := by
      simpa only [← Real.rpow_eq_pow] using hseven
    have hminus' : r * r ^ (-(5 : ℝ) / 4) = r ^ (-(1 : ℝ) / 4) := by
      simpa only [← Real.rpow_eq_pow] using hminus
    have hminus'' : r * r ^ (-(5 / 4 : ℝ)) = r ^ (-(1 / 4 : ℝ)) := by
      convert hminus' using 1 <;> ring
    rw [← hseven', ← hminus'']
    ring
  convert hfirst'.sub hmiddle' |>.add hlast' using 1
  simp only [counterexampleRadialLogDerivTwo]
  ring

@[category API, AMS 26]
private theorem hasDerivAt_counterexampleRadialAmplitude_deriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x ↦ counterexampleRadialAmplitude x *
      counterexampleRadialLogDerivOne x)
      (counterexampleRadialAmplitude r *
        (counterexampleRadialLogDerivOne r ^ 2 + counterexampleRadialLogDerivTwo r)) r := by
  convert (hasDerivAt_counterexampleRadialAmplitude hr).mul
    (hasDerivAt_counterexampleRadialLogDerivOne hr) using 1
  ring

@[category API, AMS 26]
private theorem hasFDerivAt_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ ‖w‖)
      ((z.re / ‖z‖) • Complex.reCLM + (z.im / ‖z‖) • Complex.imCLM) z := by
  have hsquare := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  have hsquare_ne : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    rw [show z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring]
    positivity
  have hsqrt := (Real.hasDerivAt_sqrt hsquare_ne).comp_hasFDerivAt z hsquare
  convert hsqrt using 1
  · ext w
    simp only [Function.comp_apply, Pi.add_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    rw [Complex.norm_def, Complex.normSq_apply]
    ring
  · ext v
    simp [Complex.norm_def, Complex.normSq_apply]
    field_simp [norm_ne_zero_iff.mpr hz]

@[category API, AMS 26]
private theorem hasFDerivAt_counterexampleRadialAmplitude_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ counterexampleRadialAmplitude ‖w‖)
      (((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
          z.re / ‖z‖) • Complex.reCLM +
        ((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
          z.im / ‖z‖) • Complex.imCLM) z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := (hasDerivAt_counterexampleRadialAmplitude hr).comp_hasFDerivAt z
    (hasFDerivAt_norm_complex hz)
  apply h.congr_fderiv
  ext v
  simp
  ring

@[category API, AMS 26]
private theorem exists_counterexampleRadialGradient_fderiv {z : ℂ} (hz : z ≠ 0) :
    ∃ R : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦
        (counterexampleRadialAmplitude ‖w‖ * counterexampleRadialLogDerivOne ‖w‖ : ℂ) *
          w / ‖w‖) R z ∧
      R 1 + Complex.I * R Complex.I =
        (counterexampleRadialAmplitude ‖z‖ *
          (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
            counterexampleRadialLogDerivTwo ‖z‖) : ℂ) * z ^ 2 / ‖z‖ ^ 2 -
          (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z ^ 2 / ‖z‖ ^ 3 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm := hasFDerivAt_norm_complex hz
  have hnorm' := Complex.ofRealCLM.hasFDerivAt.comp z hnorm
  have hAprime := (hasDerivAt_counterexampleRadialAmplitude_deriv hr).comp_hasFDerivAt z hnorm
  have hAprime' := Complex.ofRealCLM.hasFDerivAt.comp z hAprime
  have hnormInv := (hasFDerivAt_inv' (𝕜 := ℝ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).comp z hnorm'
  have hquotient := (hasFDerivAt_id z).mul hnormInv
  have hgradient := hAprime'.mul hquotient
  let Fraw : ℂ → ℂ :=
    (⇑Complex.ofRealCLM ∘
      (fun x ↦ counterexampleRadialAmplitude x * counterexampleRadialLogDerivOne x) ∘ norm) *
      (id * Inv.inv ∘ ⇑Complex.ofRealCLM ∘ fun w : ℂ ↦ ‖w‖)
  let F : ℂ → ℂ := fun w ↦
      (counterexampleRadialAmplitude ‖w‖ * counterexampleRadialLogDerivOne ‖w‖ : ℂ) *
        w / ‖w‖
  have hF : Fraw = F := by
    funext w
    simp [Fraw, F, div_eq_mul_inv]
    ring
  have hgradient' : HasFDerivAt Fraw
      (fderiv ℝ Fraw z) z := by
    have hdiffRaw : DifferentiableAt ℝ Fraw z := by
      simpa only [Fraw] using hgradient.differentiableAt
    exact hdiffRaw.hasFDerivAt
  have hdiff : DifferentiableAt ℝ F z := by
    rw [← hF]
    exact hgradient'.differentiableAt
  let R : ℂ →L[ℝ] ℂ := fderiv ℝ F z
  have hR : HasFDerivAt F R z := hdiff.hasFDerivAt
  refine ⟨R, hR, ?_⟩
  dsimp only [R]
  rw [← hF]
  dsimp only [Fraw]
  rw [hgradient.fderiv]
  simp [div_eq_mul_inv]
  field_simp [norm_ne_zero_iff.mpr hz]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring

@[category API, AMS 26]
private theorem counterexamplePrincipalBranch_sq (k : ℕ) (u : ℂ) :
    (Complex.cpow u ((k : ℂ) / 2)) ^ 2 = u ^ k := by
  change (u ^ ((k : ℂ) / 2)) ^ (2 : ℕ) = u ^ k
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast]
  congr 1
  push_cast
  ring

@[category API, AMS 26]
private theorem counterexampleAlternateBranch_sq (k : ℕ) (u : ℂ) :
    ((Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2)) ^ 2 = u ^ k := by
  rw [mul_pow, counterexamplePrincipalBranch_sq, ← pow_mul]
  conv_lhs => lhs; rw [show k * 2 = 2 * k by omega]
  rw [pow_mul, Complex.I_sq, neg_pow u k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]

@[category API, AMS 26]
private theorem cpow_half_nat_eq_or_eq_neg_alt (k : ℕ) (u : ℂ) :
    Complex.cpow u ((k : ℂ) / 2) =
        (Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2) ∨
      Complex.cpow u ((k : ℂ) / 2) =
        -((Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2)) := by
  apply eq_or_eq_neg_of_sq_eq_sq
  exact (counterexamplePrincipalBranch_sq k u).trans
    (counterexampleAlternateBranch_sq k u).symm

@[category API, AMS 26]
private theorem hasFDerivAt_counterexamplePrincipalBranch (k : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hslit : 100 / star z ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2))
      ((-((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2) / star z) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    simpa [Complex.conjCLE_apply] using Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hinvComplex : HasDerivAt (fun u : ℂ ↦ 100 / u) (-100 / (star z) ^ 2) (star z) := by
    convert (hasDerivAt_const (star z) 100).div (hasDerivAt_id (star z)) hstar0 using 1
    simp only [id_eq, zero_mul]
    field_simp
    ring
  have hinv : HasFDerivAt (fun y : ℂ ↦ 100 / star y)
      ((-100 / (star z) ^ 2) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
    simpa only [Function.comp_apply] using hinvComplex.comp_hasFDerivAt z hstar
  have hpowerComplex :=
    (hasDerivAt_id (100 / star z)).cpow_const (c := (k : ℂ) / 2) hslit
  let D : ℂ →L[ℝ] ℂ :=
    ((((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2 - 1)) *
      (-100 / (star z) ^ 2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hpower : HasFDerivAt
      (fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2)) D z := by
    simpa only [D, Function.comp_apply, id_eq, mul_one, smul_smul] using
      hpowerComplex.comp_hasFDerivAt z hinv
  apply hpower.congr_fderiv
  ext v
  have hu0 : 100 / star z ≠ 0 := div_ne_zero (by norm_num) hstar0
  dsimp only [D]
  have hcpow : Complex.cpow (100 / star z) ((k : ℂ) / 2 - 1) =
      Complex.cpow (100 / star z) ((k : ℂ) / 2) /
        Complex.cpow (100 / star z) 1 := Complex.cpow_sub _ _ hu0
  rw [hcpow]
  simp [Complex.conjCLE_apply]
  field_simp
  ring
  exact Or.inl trivial

@[category API, AMS 26]
private theorem hasFDerivAt_counterexamplePrincipalBranch_barDeriv (k : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hslit : 100 / star z ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦
      -((k : ℂ) / 2) * Complex.cpow (100 / star y) ((k : ℂ) / 2) / star y)
      ((((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
        Complex.cpow (100 / star z) ((k : ℂ) / 2) / (star z) ^ 2) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    simpa [Complex.conjCLE_apply] using Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hbranch := hasFDerivAt_counterexamplePrincipalBranch k hz hslit
  have hstarInv := (hasFDerivAt_inv' (𝕜 := ℝ) hstar0).comp z hstar
  have h := ((hasFDerivAt_const (-((k : ℂ) / 2)) z).mul hbranch).mul hstarInv
  apply h.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply, div_eq_mul_inv]
  field_simp
  ring

@[category API, AMS 26]
private theorem hasFDerivAt_counterexampleAlternateBranch (k : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hslit : -(100 / star z) ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦
      (Complex.I ^ k) * Complex.cpow (-(100 / star y)) ((k : ℂ) / 2))
      ((-((k : ℂ) / 2) *
        ((Complex.I ^ k) * Complex.cpow (-(100 / star z)) ((k : ℂ) / 2)) / star z) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hslit' : 100 / star (-z) ∈ Complex.slitPlane := by
    rw [show 100 / star (-z) = -(100 / star z) by simp; ring]
    exact hslit
  have hbase := hasFDerivAt_counterexamplePrincipalBranch k (neg_ne_zero.mpr hz) hslit'
  have hneg := hbase.comp z (hasFDerivAt_id z).neg
  have hbase_eq (y : ℂ) : 100 / star (-y) = -(100 / star y) := by
    simp
    ring
  have hfun : ((fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2)) ∘ Neg.neg) =
      fun y : ℂ ↦ Complex.cpow (-(100 / star y)) ((k : ℂ) / 2) := by
    funext y
    exact congrArg (fun u : ℂ ↦ Complex.cpow u ((k : ℂ) / 2)) (hbase_eq y)
  have hneg' := hneg.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ (congrFun hfun y).symm)
  have hraw := (hasFDerivAt_const (Complex.I ^ k) z).mul hneg'
  have hmulfun :
      ((fun _ : ℂ ↦ Complex.I ^ k) *
        fun y : ℂ ↦ Complex.cpow (-(100 / star y)) ((k : ℂ) / 2)) =
      fun y : ℂ ↦ (Complex.I ^ k) *
        Complex.cpow (-(100 / star y)) ((k : ℂ) / 2) := by
    funext y
    rfl
  rw [hmulfun] at hraw
  apply hraw.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply]
  ring

@[category API, AMS 26]
private theorem hasFDerivAt_counterexampleAlternateBranch_barDeriv (k : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hslit : -(100 / star z) ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦ -((k : ℂ) / 2) *
      ((Complex.I ^ k) * Complex.cpow (-(100 / star y)) ((k : ℂ) / 2)) / star y)
      ((((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
        ((Complex.I ^ k) * Complex.cpow (-(100 / star z)) ((k : ℂ) / 2)) /
          (star z) ^ 2) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    simpa [Complex.conjCLE_apply] using Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hbranch := hasFDerivAt_counterexampleAlternateBranch k hz hslit
  have hstarInv := (hasFDerivAt_inv' (𝕜 := ℝ) hstar0).comp z hstar
  have h := ((hasFDerivAt_const (-((k : ℂ) / 2)) z).mul hbranch).mul hstarInv
  apply h.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply, div_eq_mul_inv]
  field_simp
  ring

@[category API, AMS 26]
private theorem hasFDerivAt_radial_mul_seed_branch (W B : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hW : HasFDerivAt W ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    let G :=
      (counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          z / ‖z‖ * counterexampleSeed (W z) +
        2 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * B z
    HasFDerivAt (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y))
      (G.re • Complex.reCLM + G.im • Complex.imCLM) z := by
  dsimp only
  have hA := hasFDerivAt_counterexampleRadialAmplitude_norm hz
  have hseed := (hasFDerivAt_counterexampleSeed (W z)).comp z hW
  have hWre2 : (2 : ℂ) * ((W z).re : ℂ) = ((2 * (W z).re : ℝ) : ℂ) := by
    norm_cast
  have hWim2 : (2 : ℂ) * ((W z).im : ℂ) = ((2 * (W z).im : ℝ) : ℂ) := by
    norm_cast
  have hWim4 : (4 : ℂ) * ((W z).im : ℂ) = ((4 * (W z).im : ℝ) : ℂ) := by
    norm_cast
  apply (hA.mul hseed).congr_fderiv
  ext v
  rw [seedWirtingerModel_eq_gradient]
  simp [seedGradient, Complex.conjCLE_apply, Complex.mul_re, Complex.mul_im]
  rw [hWre2, hWim2, hWim4]
  simp only [Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re]
  ring

@[category API, AMS 26]
private theorem exists_radial_seed_gradient_fderiv (W B : ℂ → ℂ) (C : ℂ) {z : ℂ}
    (hz : z ≠ 0)
    (hW : HasFDerivAt W ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z)
    (hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    let G := fun y : ℂ ↦
      (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖ * counterexampleSeed (W y) +
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y
    ∃ G' : ℂ →L[ℝ] ℂ, HasFDerivAt G G' z ∧
      G' 1 + Complex.I * G' Complex.I =
        (counterexampleRadialAmplitude ‖z‖ : ℂ) *
            star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
          4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
          4 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
            seedWirtingerModel (W z) * B z +
          ((counterexampleRadialAmplitude ‖z‖ *
                (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                  counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
              (counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
            counterexampleSeed (W z) := by
  dsimp only
  rcases exists_counterexampleRadialGradient_fderiv hz with ⟨R, hR, hRbar⟩
  rcases exists_seedWirtingerModel_fderiv (W z) with ⟨Q, hQ, hQbar⟩
  have hAreal := hasFDerivAt_counterexampleRadialAmplitude_norm hz
  have hA0 := Complex.ofRealCLM.hasFDerivAt.comp z hAreal
  have hseedReal := (hasFDerivAt_counterexampleSeed (W z)).comp z hW
  have hseed0 := Complex.ofRealCLM.hasFDerivAt.comp z hseedReal
  have hq0 := hQ.comp z hW
  let DA : ℂ →L[ℝ] ℂ :=
    fderiv ℝ (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) z
  have hA : HasFDerivAt
      (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) DA z := by
    exact (by simpa using hA0.differentiableAt : DifferentiableAt ℝ
      (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) z).hasFDerivAt
  let Dseed : ℂ →L[ℝ] ℂ :=
    fderiv ℝ (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) z
  have hseed : HasFDerivAt
      (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Dseed z := by
    exact (by simpa using hseed0.differentiableAt : DifferentiableAt ℝ
      (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) z).hasFDerivAt
  let Dq : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦ seedWirtingerModel (W y)) z
  have hq : HasFDerivAt (fun y : ℂ ↦ seedWirtingerModel (W y)) Dq z := by
    exact (by simpa using hq0.differentiableAt : DifferentiableAt ℝ
      (fun y : ℂ ↦ seedWirtingerModel (W y)) z).hasFDerivAt
  have hone0 := hR.mul hseed
  have htwo0 := (hasFDerivAt_const (2 : ℂ) z).mul ((hA.mul hq).mul hB)
  let Done : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦
    ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
      y / ‖y‖) * counterexampleSeed (W y)) z
  have hone : HasFDerivAt (fun y : ℂ ↦
      ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
        y / ‖y‖) * counterexampleSeed (W y)) Done z := by
    exact (by simpa using hone0.differentiableAt : DifferentiableAt ℝ (fun y : ℂ ↦
      ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
        y / ‖y‖) * counterexampleSeed (W y)) z).hasFDerivAt
  let Dtwo : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦
    2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y) z
  have htwo : HasFDerivAt (fun y : ℂ ↦
      2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y)
      Dtwo z := by
    exact (by simpa [mul_assoc] using htwo0.differentiableAt : DifferentiableAt ℝ
      (fun y : ℂ ↦
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y) z).hasFDerivAt
  have hG0 := hone.add htwo
  let DG : ℂ →L[ℝ] ℂ := Done + Dtwo
  have hG : HasFDerivAt (fun y : ℂ ↦
      (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖ * counterexampleSeed (W y) +
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y)
      DG z := by
    simpa only [DG, Pi.add_apply, mul_assoc] using hG0
  have hAbar : DA 1 + Complex.I * DA Complex.I =
      (counterexampleRadialAmplitude ‖z‖ *
        counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖ := by
    let DA0 : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp
      ((((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
            z.re / ‖z‖) • Complex.reCLM) +
        (((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
            z.im / ‖z‖) • Complex.imCLM))
    have hA0' : HasFDerivAt
        (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) DA0 z := by
      simpa only [DA0, Function.comp_apply] using hA0
    have hDA : DA = DA0 := hA.unique hA0'
    rw [hDA]
    simp [DA0, Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    calc
      _ = (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          ((z.re : ℂ) + (z.im : ℂ) * Complex.I) / ‖z‖ := by ring
      _ = _ := by rw [Complex.re_add_im]
  have hseedbar : Dseed 1 + Complex.I * Dseed Complex.I =
      2 * seedWirtingerModel (W z) * B z := by
    have hcombine (a b x : ℂ) :
        a * (x.re : ℂ) + b * (x.im : ℂ) +
            Complex.I * (a * (x.im : ℂ) + -(b * (x.re : ℂ))) =
          2 * ((a - b * Complex.I) / 2) * x := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im] <;>
        ring
    let Dseed0 : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp
      ((seedGradient (W z)).comp
        ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)))
    have hseed0' : HasFDerivAt
        (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Dseed0 z := by
      simpa only [Dseed0, Function.comp_apply] using hseed0
    have hDseed : Dseed = Dseed0 := hseed.unique hseed0'
    rw [hDseed, seedWirtingerModel_eq_gradient]
    simp [Dseed0, seedGradient, Complex.ofRealCLM_apply, Complex.conjCLE_apply,
      Complex.mul_re, Complex.mul_im]
    exact hcombine _ _ _
  have hqbar : Dq 1 + Complex.I * Dq Complex.I =
      B z * star (seedTraceFreeHessianModel (W z)) / 2 := by
    let Dq0 : ℂ →L[ℝ] ℂ := Q.comp
      ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
    have hq0' : HasFDerivAt (fun y : ℂ ↦ seedWirtingerModel (W y)) Dq0 z := by
      simpa only [Dq0, Function.comp_apply] using hq0
    have hDqone : Dq0 1 = Q (B z) := by
      simp [Dq0, Complex.conjCLE_apply]
    have hDqI : Dq0 Complex.I = Q (-Complex.I * B z) := by
      dsimp only [Dq0]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I by
        simp [Complex.conjCLE_apply]]
      congr 1
      ring
    have hDq : Dq = Dq0 := hq.unique hq0'
    rw [hDq]
    rw [hDqone, hDqI]
    exact hQbar (B z)
  have hBbar : (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) 1 +
      Complex.I * (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) Complex.I = 2 * C := by
    simp [Complex.conjCLE_apply]
    rw [show Complex.I * (C * Complex.I) = -C by
      rw [show Complex.I * (C * Complex.I) = C * Complex.I ^ 2 by ring,
        Complex.I_sq]
      ring]
    ring
  have honebar : Done 1 + Complex.I * Done Complex.I =
      ((counterexampleRadialAmplitude ‖z‖ *
            (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
              counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
          (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
        counterexampleSeed (W z) +
      2 * ((counterexampleRadialAmplitude ‖z‖ *
          counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
        seedWirtingerModel (W z) * B z := by
    let Done0 : ℂ →L[ℝ] ℂ := fderiv ℝ
      ((fun y : ℂ ↦
        (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) z
    have hone0Raw : HasFDerivAt
        ((fun y : ℂ ↦
          (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Done0 z := by
      exact hone0.differentiableAt.hasFDerivAt
    have honeFun :
        ((fun y : ℂ ↦
          (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) =
        fun y : ℂ ↦
          ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * counterexampleSeed (W y) := by
      rfl
    have hone0' : HasFDerivAt (fun y : ℂ ↦
        ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖) * counterexampleSeed (W y)) Done0 z := by
      rw [← honeFun]
      exact hone0Raw
    have hDone : Done = Done0 := hone.unique hone0'
    rw [hDone]
    dsimp only [Done0]
    rw [hone0.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [show
      ((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          z / ‖z‖) * Dseed 1 + (counterexampleSeed (W z) : ℂ) * R 1 +
          Complex.I *
            (((counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖) *
                Dseed Complex.I + (counterexampleSeed (W z) : ℂ) * R Complex.I) =
        ((counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖) *
            (Dseed 1 + Complex.I * Dseed Complex.I) +
          (counterexampleSeed (W z) : ℂ) *
            (R 1 + Complex.I * R Complex.I) by ring]
    rw [hRbar, hseedbar]
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  have htwobar : Dtwo 1 + Complex.I * Dtwo Complex.I =
      (counterexampleRadialAmplitude ‖z‖ : ℂ) *
          star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
        4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
        2 * ((counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
          seedWirtingerModel (W z) * B z := by
    let Dtwo0 : ℂ →L[ℝ] ℂ := fderiv ℝ
      ((fun _ : ℂ ↦ (2 : ℂ)) *
        (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
          fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) z
    have htwo0Raw : HasFDerivAt
        ((fun _ : ℂ ↦ (2 : ℂ)) *
          (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
            fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) Dtwo0 z := by
      exact htwo0.differentiableAt.hasFDerivAt
    have htwoFun :
        ((fun _ : ℂ ↦ (2 : ℂ)) *
          (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
            fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) =
        fun y : ℂ ↦
          2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y := by
      funext y
      simp only [Pi.mul_apply]
      ring
    have htwo0' : HasFDerivAt (fun y : ℂ ↦
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y) Dtwo0 z := by
      rw [← htwoFun]
      exact htwo0Raw
    have hDtwo : Dtwo = Dtwo0 := htwo.unique htwo0'
    rw [hDtwo]
    dsimp only [Dtwo0]
    rw [htwo0.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Pi.mul_apply, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
    have hBbar' : C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 +
        Complex.I * (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I) = 2 * C := by
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hBbar
    rw [show
      2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z) *
            (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1) +
          B z * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * Dq 1 +
            seedWirtingerModel (W z) * DA 1)) +
        Complex.I *
          (2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z) *
              (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I) +
            B z * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * Dq Complex.I +
              seedWirtingerModel (W z) * DA Complex.I))) =
        2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z)) *
            (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 +
              Complex.I * (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I)) +
          2 * B z *
            ((counterexampleRadialAmplitude ‖z‖ : ℂ) *
                (Dq 1 + Complex.I * Dq Complex.I) +
              seedWirtingerModel (W z) * (DA 1 + Complex.I * DA Complex.I)) by ring,
      hBbar', hqbar, hAbar]
    simp only [Complex.ofReal_mul]
    ring
  have hDG : DG = Done + Dtwo := by
    rfl
  refine ⟨DG, hG, ?_⟩
  rw [hDG]
  simp only [ContinuousLinearMap.add_apply]
  rw [show Done 1 + Dtwo 1 + Complex.I * (Done Complex.I + Dtwo Complex.I) =
    (Done 1 + Complex.I * Done Complex.I) +
      (Dtwo 1 + Complex.I * Dtwo Complex.I) by ring,
    honebar, htwobar]
  ring

@[category API, AMS 26]
private theorem traceFreeHessian_radial_mul_seed_branch (W B : ℂ → ℂ) (C : ℂ) (D : ℝ)
    {z : ℂ} (hz : z ≠ 0)
    (hW : ∀ᶠ y in 𝓝 z,
      HasFDerivAt W ((B y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y)
    (hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    traceFreeHessian
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D) z =
        (counterexampleRadialAmplitude ‖z‖ : ℂ) *
            star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
          4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
          4 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
            seedWirtingerModel (W z) * B z +
          ((counterexampleRadialAmplitude ‖z‖ *
                (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                  counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
              (counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
            counterexampleSeed (W z) := by
  let G := fun y : ℂ ↦
    (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
        y / ‖y‖ * counterexampleSeed (W y) +
      2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y
  have hWz := hW.self_of_nhds
  rcases exists_radial_seed_gradient_fderiv W B C hz hWz hB with ⟨G', hG, hGbar⟩
  have hfirst : ∀ᶠ y in 𝓝 z, HasFDerivAt
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D)
      ((G y).re • Complex.reCLM + (G y).im • Complex.imCLM) y := by
    filter_upwards [hW, eventually_ne_nhds hz] with y hWy hy
    simpa [G] using (hasFDerivAt_radial_mul_seed_branch W B hy hWy).add_const D
  have hre := Complex.reCLM.hasFDerivAt.comp z hG
  have him := Complex.imCLM.hasFDerivAt.comp z hG
  have hgradient := (hre.smul_const Complex.reCLM).add (him.smul_const Complex.imCLM)
  have hfirst' : fderiv ℝ
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D) =ᶠ[𝓝 z]
      (fun y ↦ (G y).re • Complex.reCLM + (G y).im • Complex.imCLM) :=
    hfirst.mono fun _ hy ↦ hy.fderiv
  have hsymm : (G' Complex.I).re = (G' 1).im := by
    have h := second_derivative_symmetric_of_eventually_of_real hfirst hgradient
      (1 : ℂ) Complex.I
    simpa using h.symm
  rw [traceFreeHessian, (hgradient.congr_of_eventuallyEq hfirst').fderiv]
  simp
  have hcontract :
      ((G' 1).re : ℂ) - ((G' Complex.I).im : ℂ) +
          2 * ((G' 1).im : ℂ) * Complex.I = G' 1 + Complex.I * G' Complex.I := by
    apply Complex.ext <;> simp [hsymm] <;> ring
  rw [hcontract, hGbar]
  push_cast
  simp only [starRingEnd_apply]

/-- The dominant part of the trace-free Hessian on the punctured plane. -/
private noncomputable def counterexampleHessianLeading (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  (counterexampleRadialAmplitude r : ℂ) * star (seedTraceFreeHessianModel w) *
    (-((k : ℂ) / 2) * w / star z) ^ 2

/-- The lower-order part of the trace-free Hessian on a local analytic branch. -/
private noncomputable def counterexampleHessianError (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  let wbar := -((k : ℂ) / 2) * w / star z
  let wbarbar := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2
  let A := counterexampleRadialAmplitude r
  let L₁ := counterexampleRadialLogDerivOne r
  let L₂ := counterexampleRadialLogDerivTwo r
  let Abar : ℂ := (A * L₁ : ℝ) * z / (2 * r)
  let Abarbar : ℂ :=
    (A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2) -
      (A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)
  4 * A * seedWirtingerModel w * wbarbar +
    8 * Abar * seedWirtingerModel w * wbar +
    4 * Abarbar * counterexampleSeed w

@[category API, AMS 26]
private theorem counterexampleRadialAmplitude_pos {r : ℝ} (hr : 0 < r) :
    0 < counterexampleRadialAmplitude r := by
  simp only [counterexampleRadialAmplitude]
  positivity

/-- A radial upper bound for the three lower-order Hessian terms. -/
@[category API, AMS 26]
private theorem counterexampleHessianError_raw_bound (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖counterexampleHessianError k z‖ ≤
      counterexampleRadialAmplitude ‖z‖ * (129 / 20) * ((k : ℝ) / 2) *
          (((k : ℝ) / 2) + 1) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ / ‖z‖ ^ 2 +
        counterexampleRadialAmplitude ‖z‖ * (903 / 20) * ((k : ℝ) / 2) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ *
          ‖z‖ ^ (-(9 : ℝ) / 4) +
        counterexampleRadialAmplitude ‖z‖ * (8349 / 80) *
          ‖z‖ ^ (-(5 : ℝ) / 2) := by
  let r := ‖z‖
  let p := (k : ℝ) / 2
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  let A := counterexampleRadialAmplitude r
  let L₁ := counterexampleRadialLogDerivOne r
  let L₂ := counterexampleRadialLogDerivTwo r
  have hr : 0 < r := by simpa only [r] using norm_pos_iff.mpr hz
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hA : 0 < A := by exact counterexampleRadialAmplitude_pos hr
  have hL := counterexampleRadialLogDeriv_bounds hr (by simpa only [r] using hz1)
  have hwbar : ‖-((k : ℂ) / 2) * w / star z‖ = p * ‖w‖ / r := by
    have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpCast]
    simp only [norm_div, norm_mul, norm_neg, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp, show ‖z‖ = r by rfl]
  have hwbarbar :
      ‖((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2‖ =
        p * (p + 1) * ‖w‖ / r ^ 2 := by
    have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpCast, show ((p : ℂ) + 1) = (((p + 1 : ℝ) : ℂ)) by push_cast; ring]
    simp only [norm_div, norm_mul, norm_pow, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp, abs_of_pos (by positivity : 0 < p + 1),
      show ‖z‖ = r by rfl]
  let Abar : ℂ := (A * L₁ : ℝ) * z / (2 * r)
  let Abarbar : ℂ :=
    (A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2) -
      (A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)
  have hAbar : ‖Abar‖ ≤ A * (7 / 2) * r ^ (-(5 : ℝ) / 4) := by
    have hAbarNorm : ‖Abar‖ = A * |L₁| / 2 := by
      dsimp only [Abar]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos hA,
        show ‖z‖ = r by rfl]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      norm_num
      field_simp [hr.ne']
    rw [hAbarNorm]
    calc
      A * |L₁| / 2 ≤ A * (7 * r ^ (-(5 : ℝ) / 4)) / 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.1 hA.le) (by norm_num)
      _ = A * (7 / 2) * r ^ (-(5 : ℝ) / 4) := by ring
  have hpowNineFive : r ^ (-(9 : ℝ) / 4) ≤ r ^ (-(5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hr (by simpa only [r] using hz1) (by norm_num)
  have hpowSquare : (r ^ (-(5 : ℝ) / 4)) ^ 2 = r ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    ring
  have hAbarbar : ‖Abarbar‖ ≤ A * (66 / 4) * r ^ (-(5 : ℝ) / 2) := by
    calc
      ‖Abarbar‖ ≤
          ‖(A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2)‖ +
            ‖(A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)‖ := by
        exact norm_sub_le _ _
      _ = A / 4 * (|L₁ ^ 2 + L₂| + |L₁| / r) := by
        rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
          Complex.norm_real, Complex.norm_real, norm_pow, norm_pow,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos hA, show ‖z‖ = r by rfl]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        norm_num
        field_simp [hr.ne']
        rw [abs_of_pos hr]
        ring
      _ ≤ A / 4 *
          ((7 * r ^ (-(5 : ℝ) / 4)) ^ 2 +
            10 * r ^ (-(9 : ℝ) / 4) +
            7 * r ^ (-(5 : ℝ) / 4) / r) := by
        gcongr
        · exact (abs_add_le _ _).trans <| add_le_add
            (by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg L₁) hL.1 2)
            hL.2
        · exact hL.1
      _ ≤ A * (66 / 4) * r ^ (-(5 : ℝ) / 2) := by
        have hdiv : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 : ℝ) / 4) := by
          have h := Real.rpow_sub hr (-(5 : ℝ) / 4) 1
          rw [Real.rpow_one] at h
          rw [← h]
          congr 1
          ring
        rw [mul_pow, hpowSquare]
        have hsum : 7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
            10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(9 : ℝ) / 4) ≤
            66 * r ^ (-(5 : ℝ) / 2) := by
          nlinarith only [hpowNineFive]
        calc
          A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
              10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(5 : ℝ) / 4) / r) =
              A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
                10 * r ^ (-(9 : ℝ) / 4) + 7 * (r ^ (-(5 : ℝ) / 4) / r)) := by
            ring
          _ = A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
              10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(9 : ℝ) / 4)) := by rw [hdiv]
          _ ≤ A / 4 * (66 * r ^ (-(5 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = _ := by ring
  have htermOne :
      ‖4 * A * seedWirtingerModel w *
          (((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2)‖ ≤
        A * (129 / 20) * p * (p + 1) * ‖w‖ / r ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hwbarbar]
    norm_num [abs_of_pos hA]
    calc
      4 * A * ‖seedWirtingerModel w‖ * (p * (p + 1) * ‖w‖ / r ^ 2) ≤
          4 * A * (129 / 80) * (p * (p + 1) * ‖w‖ / r ^ 2) := by
        gcongr
        exact norm_seedWirtingerModel_le w
      _ = _ := by ring
  have htermTwo :
      ‖8 * Abar * seedWirtingerModel w * (-((k : ℂ) / 2) * w / star z)‖ ≤
        A * (903 / 20) * p * ‖w‖ * r ^ (-(9 : ℝ) / 4) := by
    rw [norm_mul, norm_mul, norm_mul, hwbar]
    norm_num
    calc
      8 * ‖Abar‖ * ‖seedWirtingerModel w‖ * (p * ‖w‖ / r) ≤
          8 * (A * (7 / 2) * r ^ (-(5 : ℝ) / 4)) * (129 / 80) *
            (p * ‖w‖ / r) := by gcongr; exact norm_seedWirtingerModel_le w
      _ = A * (903 / 20) * p * ‖w‖ * r ^ (-(9 / 4 : ℝ)) := by
        have hdiv : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 : ℝ) / 4) := by
          have h := Real.rpow_sub hr (-(5 : ℝ) / 4) 1
          rw [Real.rpow_one] at h
          rw [← h]
          congr 1
          ring
        have hExp : r ^ (-(9 : ℝ) / 4) = r ^ (-(9 / 4 : ℝ)) := by
          congr 1
          ring
        have hdiv' : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 / 4 : ℝ)) :=
          hdiv.trans hExp
        calc
          8 * (A * (7 / 2) * r ^ (-(5 : ℝ) / 4)) * (129 / 80) *
              (p * ‖w‖ / r) =
              A * (903 / 20) * p * ‖w‖ *
                (r ^ (-(5 : ℝ) / 4) / r) := by ring
          _ = A * (903 / 20) * p * ‖w‖ * r ^ (-(9 / 4 : ℝ)) :=
            congrArg (fun x : ℝ ↦ A * (903 / 20) * p * ‖w‖ * x) hdiv'
  have htermThree : ‖4 * Abarbar * counterexampleSeed w‖ ≤
      A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    calc
      4 * ‖Abarbar‖ * |counterexampleSeed w| ≤
          4 * (A * (66 / 4) * r ^ (-(5 : ℝ) / 2)) * (253 / 160) := by
        gcongr
        exact counterexampleSeed_abs_le w
      _ = _ := by ring
  simp only [counterexampleHessianError]
  dsimp only [r, p, w, A, L₁, L₂, Abar, Abarbar] at *
  calc
    ‖4 * counterexampleRadialAmplitude ‖z‖ *
          seedWirtingerModel (Complex.cpow (100 / star z) ((k : ℂ) / 2)) *
          (((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
            Complex.cpow (100 / star z) ((k : ℂ) / 2) / (star z) ^ 2) +
        8 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / (2 * ‖z‖)) *
          seedWirtingerModel (Complex.cpow (100 / star z) ((k : ℂ) / 2)) *
          (-((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2) / star z) +
        4 * ((counterexampleRadialAmplitude ‖z‖ *
              (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 /
              (4 * ‖z‖ ^ 2) -
            (counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 /
              (4 * ‖z‖ ^ 3)) *
          counterexampleSeed (Complex.cpow (100 / star z) ((k : ℂ) / 2))‖ ≤
        _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add htermOne htermTwo) htermThree

@[category API, AMS 26]
private theorem counterexampleBranch_norm (k : ℕ) (z : ℂ) :
    ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ =
      (100 / ‖z‖) ^ ((k : ℝ) / 2) := by
  rw [Complex.cpow_eq_pow,
    show ((k : ℂ) / 2) = (((k : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, norm_div, norm_star]
  norm_num

@[category API, AMS 26]
private theorem counterexampleHessianLeading_lower_bound (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) :
    counterexampleRadialAmplitude ‖z‖ * (7 / 50) *
        (((k : ℝ) / 2) ^ 2 *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ ^ 2 / ‖z‖ ^ 2) ≤
      ‖counterexampleHessianLeading k z‖ := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hA := counterexampleRadialAmplitude_pos (norm_pos_iff.mpr hz)
  have hsquare :
      ((k : ℝ) / 2) ^ 2 *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ ^ 2 / ‖z‖ ^ 2 =
        (((k : ℝ) / 2) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ / ‖z‖) ^ 2 := by
    ring
  rw [hsquare]
  simp only [counterexampleHessianLeading, norm_mul, norm_star, norm_pow, norm_neg,
    norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  norm_num [abs_of_nonneg hk0]
  rw [abs_of_pos hA]
  gcongr
  exact seven_div_fifty_le_norm_seedTraceFreeHessianModel _

@[category API, AMS 26]
private theorem counterexampleHessianLeading_ne_zero (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) : counterexampleHessianLeading k z ≠ 0 := by
  rw [← norm_pos_iff]
  have hW : Complex.cpow (100 / star z) ((k : ℂ) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  have hlower := counterexampleHessianLeading_lower_bound k hk hz
  refine lt_of_lt_of_le ?_ hlower
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hA := counterexampleRadialAmplitude_pos (norm_pos_iff.mpr hz)
  positivity

/-- The three error terms are bounded by the leading term times a sum of positive powers of
the radius. -/
@[category API, AMS 26]
private theorem counterexampleHessianError_le_leading_mul_ratio (k : ℕ) (hk : 0 < k)
    {z : ℂ} (hz : z ≠ 0) (hz_one : ‖z‖ ≤ 1) :
    ‖counterexampleHessianError k z‖ ≤ ‖counterexampleHessianLeading k z‖ *
      (140 * ‖z‖ ^ ((k : ℝ) / 2) +
        645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
        3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) := by
  let r := ‖z‖
  let p := (k : ℝ) / 2
  let W := ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖
  let A := counterexampleRadialAmplitude r
  let D := A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)
  have hr : 0 < r := by simpa only [r] using norm_pos_iff.mpr hz
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) / 2 ≤ p := by
    dsimp only [p]
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hA : 0 < A := counterexampleRadialAmplitude_pos hr
  have hW : 0 < W := by
    dsimp only [W]
    rw [norm_pos_iff]
    exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  have hscale : 1 ≤ r ^ p * W := by
    calc
      1 ≤ (100 : ℝ) ^ p := Real.one_le_rpow (by norm_num) hp0.le
      _ = r ^ p * (100 / r) ^ p := by
        rw [Real.div_rpow (by norm_num) hr.le]
        field_simp [(Real.rpow_pos_of_pos hr p).ne']
      _ = r ^ p * W := by
        dsimp only [W, r, p]
        rw [counterexampleBranch_norm]
  have hraw : ‖counterexampleHessianError k z‖ ≤
      A * (129 / 20) * p * (p + 1) * W / r ^ 2 +
        A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) +
        A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := by
    simpa only [A, W, p, r] using counterexampleHessianError_raw_bound k hk hz hz_one
  have hcoeffOne : (129 / 20) * p * (p + 1) ≤ (98 / 5) * p ^ 2 := by
    nlinarith only [hp]
  have hcoeffTwo : (903 / 20) * p ≤ (903 / 10) * p ^ 2 := by
    nlinarith only [hp]
  have hcoeffThree : (8349 / 80) ≤ 420 * p ^ 2 := by
    nlinarith only [hp, sq_nonneg (p - 1 / 2)]
  have hpowTwo : r ^ (p - 1 / 4) / r ^ 2 =
      r ^ p * r ^ (-(9 : ℝ) / 4) := by
    calc
      r ^ (p - 1 / 4) / r ^ 2 = r ^ (p - 1 / 4) / r ^ (2 : ℝ) :=
        congrArg (fun x : ℝ ↦ r ^ (p - 1 / 4) / x) (Real.rpow_natCast r 2).symm
      _ = r ^ ((p - 1 / 4) - 2) :=
        (Real.rpow_sub hr _ _).symm
      _ = r ^ (p + (-(9 : ℝ) / 4)) := by congr 1; ring
      _ = r ^ p * r ^ (-(9 : ℝ) / 4) := Real.rpow_add hr _ _
  have hpowThree : r ^ ((k : ℝ) - 1 / 2) / r ^ 2 =
      (r ^ p) ^ 2 * r ^ (-(5 : ℝ) / 2) := by
    calc
      r ^ ((k : ℝ) - 1 / 2) / r ^ 2 =
          r ^ ((k : ℝ) - 1 / 2) / r ^ (2 : ℝ) :=
        congrArg (fun x : ℝ ↦ r ^ ((k : ℝ) - 1 / 2) / x)
          (Real.rpow_natCast r 2).symm
      _ = r ^ (((k : ℝ) - 1 / 2) - 2) := (Real.rpow_sub hr _ _).symm
      _ = r ^ (p + p + (-(5 : ℝ) / 2)) := by
        congr 1
        dsimp only [p]
        ring
      _ = (r ^ p) ^ 2 * r ^ (-(5 : ℝ) / 2) := by
        rw [Real.rpow_add hr, Real.rpow_add hr]
        ring
  have htermOne : A * (129 / 20) * p * (p + 1) * W / r ^ 2 ≤
      D * (140 * r ^ p) := by
    have hbase : 0 ≤ A * (98 / 5) * p ^ 2 * W / r ^ 2 := by positivity
    calc
      A * (129 / 20) * p * (p + 1) * W / r ^ 2 ≤
          A * (98 / 5) * p ^ 2 * W / r ^ 2 := by
        calc
          _ = (A * W / r ^ 2) * ((129 / 20) * p * (p + 1)) := by ring
          _ ≤ (A * W / r ^ 2) * ((98 / 5) * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffOne (by positivity)
          _ = _ := by ring
      _ ≤ (A * (98 / 5) * p ^ 2 * W / r ^ 2) * (r ^ p * W) :=
        le_mul_of_one_le_right hbase hscale
      _ = D * (140 * r ^ p) := by
        dsimp only [D]
        ring
  have htargetTwo : D * (645 * r ^ (p - 1 / 4)) =
      (A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4)) * (r ^ p * W) := by
    dsimp only [D]
    calc
      (A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)) *
            (645 * r ^ (p - 1 / 4)) =
          A * (903 / 10) * p ^ 2 * W ^ 2 *
            (r ^ (p - 1 / 4) / r ^ 2) := by ring
      _ = _ := by rw [hpowTwo]; ring
  have htermTwo : A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) ≤
      D * (645 * r ^ (p - 1 / 4)) := by
    have hbase : 0 ≤ A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4) := by
      positivity
    calc
      A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) ≤
          A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4) := by
        calc
          _ = (A * W * r ^ (-(9 : ℝ) / 4)) * ((903 / 20) * p) := by ring
          _ ≤ (A * W * r ^ (-(9 : ℝ) / 4)) * ((903 / 10) * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffTwo (by positivity)
          _ = _ := by ring
      _ ≤ (A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4)) *
          (r ^ p * W) := le_mul_of_one_le_right hbase hscale
      _ = D * (645 * r ^ (p - 1 / 4)) := htargetTwo.symm
  have hscaleSquare : 1 ≤ (r ^ p * W) ^ 2 := by nlinarith only [hscale]
  have htargetThree : D * (3000 * r ^ ((k : ℝ) - 1 / 2)) =
      (A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2)) * (r ^ p * W) ^ 2 := by
    dsimp only [D]
    calc
      (A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)) *
            (3000 * r ^ ((k : ℝ) - 1 / 2)) =
          A * 420 * p ^ 2 * W ^ 2 *
            (r ^ ((k : ℝ) - 1 / 2) / r ^ 2) := by ring
      _ = _ := by rw [hpowThree]; ring
  have htermThree : A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) ≤
      D * (3000 * r ^ ((k : ℝ) - 1 / 2)) := by
    have hbase : 0 ≤ A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2) := by positivity
    calc
      A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) ≤
          A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2) := by
        calc
          _ = (A * r ^ (-(5 : ℝ) / 2)) * (8349 / 80) := by ring
          _ ≤ (A * r ^ (-(5 : ℝ) / 2)) * (420 * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffThree (by positivity)
          _ = _ := by ring
      _ ≤ (A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2)) * (r ^ p * W) ^ 2 :=
        le_mul_of_one_le_right hbase hscaleSquare
      _ = D * (3000 * r ^ ((k : ℝ) - 1 / 2)) := htargetThree.symm
  have hratioNonneg : 0 ≤
      140 * r ^ p + 645 * r ^ (p - 1 / 4) +
        3000 * r ^ ((k : ℝ) - 1 / 2) := by positivity
  have hlower : D ≤ ‖counterexampleHessianLeading k z‖ := by
    simpa only [D, A, W, p, r] using counterexampleHessianLeading_lower_bound k hk hz
  calc
    ‖counterexampleHessianError k z‖ ≤
        A * (129 / 20) * p * (p + 1) * W / r ^ 2 +
          A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) +
          A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := hraw
    _ ≤ D * (140 * r ^ p) + D * (645 * r ^ (p - 1 / 4)) +
        D * (3000 * r ^ ((k : ℝ) - 1 / 2)) :=
      add_le_add (add_le_add htermOne htermTwo) htermThree
    _ = D * (140 * r ^ p + 645 * r ^ (p - 1 / 4) +
        3000 * r ^ ((k : ℝ) - 1 / 2)) := by ring
    _ ≤ ‖counterexampleHessianLeading k z‖ *
        (140 * r ^ p + 645 * r ^ (p - 1 / 4) +
          3000 * r ^ ((k : ℝ) - 1 / 2)) :=
      mul_le_mul_of_nonneg_right hlower hratioNonneg
    _ = ‖counterexampleHessianLeading k z‖ *
        (140 * ‖z‖ ^ ((k : ℝ) / 2) +
          645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
          3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) := by rfl

/-- The Hessian error is eventually strictly smaller than the leading term. -/
@[category API, AMS 26]
private theorem counterexampleHessianError_lt_leading_eventually (k : ℕ) (hk : 0 < k) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ‖counterexampleHessianError k z‖ < ‖counterexampleHessianLeading k z‖ := by
  rcases counterexample_error_powers_tendsto_zero k hk with
    ⟨hhalf, hquarter, hminus⟩
  have hratio : Tendsto
      (fun z : ℂ ↦ 140 * ‖z‖ ^ ((k : ℝ) / 2) +
        645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
        3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (((hhalf.const_mul (140 : ℝ)).add (hquarter.const_mul (645 : ℝ))).add
        (hminus.const_mul (3000 : ℝ)))
  have hnormAt : ContinuousAt (fun z : ℂ ↦ ‖z‖) 0 := continuous_norm.continuousAt
  have hnorm : Tendsto (fun z : ℂ ↦ ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hnormAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  filter_upwards [hratio.eventually_lt_const zero_lt_one,
    hnorm.eventually_lt_const zero_lt_one, self_mem_nhdsWithin] with z hR hz_one hz
  have hz' : z ≠ 0 := by simpa using hz
  have hlead : 0 < ‖counterexampleHessianLeading k z‖ :=
    norm_pos_iff.mpr (counterexampleHessianLeading_ne_zero k hk hz')
  calc
    ‖counterexampleHessianError k z‖ ≤
        ‖counterexampleHessianLeading k z‖ *
          (140 * ‖z‖ ^ ((k : ℝ) / 2) +
            645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
            3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) :=
      counterexampleHessianError_le_leading_mul_ratio k hk hz' hz_one.le
    _ < ‖counterexampleHessianLeading k z‖ * 1 := mul_lt_mul_of_pos_left hR hlead
    _ = ‖counterexampleHessianLeading k z‖ := mul_one _

/-- On either analytic square-root branch, the trace-free Hessian is the displayed dominant
term plus the three lower-order product-and-chain-rule terms. -/
@[category API, AMS 26]
private theorem counterexample_traceFreeHessian_decomposition (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    traceFreeHessian (counterexample k) z =
      counterexampleHessianLeading k z + counterexampleHessianError k z := by
  let U : ℂ → ℂ := fun y ↦ 100 / star y
  let W : ℂ → ℂ := fun y ↦ Complex.cpow (U y) ((k : ℂ) / 2)
  let B : ℂ → ℂ := fun y ↦ -((k : ℂ) / 2) * W y / star y
  let C : ℂ := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * W z / (star z) ^ 2
  have hU0 : U z ≠ 0 :=
    div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hU0 with hslit | hslit
  · have hUcont : ContinuousAt U z := by
      dsimp [U]
      fun_prop (disch := aesop)
    have hW : ∀ᶠ y in 𝓝 z,
        HasFDerivAt W ((B y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
      filter_upwards [hUcont (Complex.isOpen_slitPlane.mem_nhds hslit),
        eventually_ne_nhds hz] with y hyU hy
      simpa [U, W, B] using hasFDerivAt_counterexamplePrincipalBranch k hy hyU
    have hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
      simpa [U, W, B, C] using
        hasFDerivAt_counterexamplePrincipalBranch_barDeriv k hz hslit
    have htrace := traceFreeHessian_radial_mul_seed_branch W B C (10 ^ 10) hz hW hB
    have hcounterexample : counterexample k = fun y : ℂ ↦
        counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + 10 ^ 10 := by
      funext y
      simp [counterexample, counterexampleRadialAmplitude, U, W]
      ring
    rw [hcounterexample, htrace]
    simp only [counterexampleHessianLeading, counterexampleHessianError]
    dsimp only [U, W, B, C]
    field_simp [norm_ne_zero_iff.mpr hz]
    ring
  · let W' : ℂ → ℂ := fun y ↦
      (Complex.I ^ k) * Complex.cpow (-U y) ((k : ℂ) / 2)
    let B' : ℂ → ℂ := fun y ↦ -((k : ℂ) / 2) * W' y / star y
    let C' : ℂ := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * W' z / (star z) ^ 2
    have hUcont : ContinuousAt (fun y ↦ -U y) z := by
      dsimp [U]
      fun_prop (disch := aesop)
    have hW' : ∀ᶠ y in 𝓝 z,
        HasFDerivAt W' ((B' y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
      filter_upwards [hUcont (Complex.isOpen_slitPlane.mem_nhds hslit),
        eventually_ne_nhds hz] with y hyU hy
      simpa [U, W', B'] using hasFDerivAt_counterexampleAlternateBranch k hy hyU
    have hB' : HasFDerivAt B' (C' • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
      simpa [U, W', B', C'] using
        hasFDerivAt_counterexampleAlternateBranch_barDeriv k hz hslit
    have htrace := traceFreeHessian_radial_mul_seed_branch W' B' C' (10 ^ 10) hz hW' hB'
    have hcounterexample : counterexample k = fun y : ℂ ↦
        counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W' y) + 10 ^ 10 := by
      funext y
      simp only [counterexample]
      have hseed : counterexampleSeed (Complex.cpow (U y) ((k : ℂ) / 2)) =
          counterexampleSeed
            ((Complex.I ^ k) * Complex.cpow (-U y) ((k : ℂ) / 2)) := by
        simpa only [← Complex.cpow_eq_pow] using counterexampleSeed_cpow_eq_alt k (U y)
      rw [hseed]
      simp [counterexampleRadialAmplitude, U, W']
      ring
    rw [hcounterexample]
    have hrelation := cpow_half_nat_eq_or_eq_neg_alt k (U z)
    rcases hrelation with hrelation | hrelation
    · have hWvalue : W z = W' z := by simpa [W, W', U] using hrelation
      rw [htrace]
      dsimp only [B', C']
      rw [← hWvalue]
      simp only [counterexampleHessianLeading, counterexampleHessianError]
      dsimp only [U, W, B, C]
      field_simp [norm_ne_zero_iff.mpr hz]
      ring
    · have hWvalue : W' z = -W z := by
        have hneg := congrArg Neg.neg hrelation
        simpa [W, W', U] using hneg.symm
      rw [htrace]
      dsimp only [B', C']
      rw [hWvalue]
      simp only [seedTraceFreeHessianModel_neg, seedWirtingerModel_neg,
        counterexampleSeed_neg]
      simp only [counterexampleHessianLeading, counterexampleHessianError]
      dsimp only [U, W, B, C]
      field_simp [norm_ne_zero_iff.mpr hz]
      ring

/-- The trace-free Hessian of a smooth member of the family is continuous. -/
@[category API, AMS 26]
private theorem continuous_traceFreeHessian_counterexample (k : ℕ) (hk : 0 < k) :
    Continuous (traceFreeHessian (counterexample k)) := by
  have hfirst : ContDiff ℝ ∞ (fderiv ℝ (counterexample k)) :=
    (contDiff_infty_iff_fderiv.mp (counterexample_contDiff k hk)).2
  have hsecond : Continuous
      (fderiv ℝ (fun z ↦ fderiv ℝ (counterexample k) z)) :=
    hfirst.continuous_fderiv (by simp)
  unfold traceFreeHessian
  fun_prop

/-- The principal-branch leading term on a circle admits a continuous representative and an
argument lift. The representative uses the continuous half-power branch
`(100/r)^(k/2) exp(i(k/2)t)`, including when `k` is odd. -/
@[category API, AMS 26]
private theorem exists_continuous_counterexampleHessianLeading_circle
    (k : ℕ) (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ t, L t = counterexampleHessianLeading k
        ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) ∧
      L (2 * Real.pi) = L 0 ∧
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = L t / ‖L t‖) ∧
        θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  let p : ℝ := (k : ℝ) / 2
  let a : ℝ := (100 / r) ^ p
  let zcircle : ℝ → ℂ := fun t ↦
    (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  let w : ℝ → ℂ := fun t ↦
    (a : ℂ) * Complex.exp (((p * t : ℝ) : ℂ) * Complex.I)
  let S : ℝ := counterexampleRadialAmplitude r * p ^ 2 * a ^ 2 / r ^ 2
  let L : ℝ → ℂ := fun t ↦
    (S : ℂ) *
      Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      star (seedTraceFreeHessianModel (w t))
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hS : 0 < S := by
    dsimp only [S]
    have hA := counterexampleRadialAmplitude_pos hr
    positivity
  have hzNorm (t : ℝ) : ‖zcircle t‖ = r := by
    dsimp only [zcircle]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
    simp [Complex.mul_re]
  have hzNe (t : ℝ) : zcircle t ≠ 0 := by
    rw [← norm_pos_iff, hzNorm]
    exact hr
  have hstar (t : ℝ) : star (zcircle t) =
      (r : ℂ) * Complex.exp (-((t : ℂ) * Complex.I)) := by
    change (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) = _
    rw [map_mul, ← Complex.exp_conj]
    simp
  have hU (t : ℝ) : 100 / star (zcircle t) =
      ((100 / r : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [hstar, div_eq_mul_inv, mul_inv, Complex.exp_neg, inv_inv]
    push_cast
    field_simp [hr.ne']
  have haSq : a ^ 2 = (100 / r) ^ k := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 100 / r)]
    have hpTwo : p * (2 : ℕ) = (k : ℝ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpTwo, Real.rpow_natCast]
  have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
    dsimp only [p]
    push_cast
    ring
  have hwsq (t : ℝ) : w t ^ 2 =
      Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2 := by
    rw [counterexamplePrincipalBranch_sq, hU, mul_pow]
    rw [mul_pow]
    have haSqC : (a : ℂ) ^ 2 = (((100 / r) ^ k : ℝ) : ℂ) := by
      exact_mod_cast haSq
    have hbasePowC : ((100 / r : ℝ) : ℂ) ^ k =
        (((100 / r) ^ k : ℝ) : ℂ) := by norm_cast
    rw [haSqC, hbasePowC, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    dsimp only [p]
    push_cast
    ring
  have hmodel (t : ℝ) : seedTraceFreeHessianModel (w t) =
      seedTraceFreeHessianModel
        (Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2)) := by
    have hbranches : w t = Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ∨
        w t = -Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      exact hwsq t
    rcases hbranches with hbranch | hbranch
    · rw [hbranch]
    · rw [hbranch, seedTraceFreeHessianModel_neg]
  have hphaseFactor (t : ℝ) :
      Complex.exp (((p * t : ℝ) : ℂ) * Complex.I) ^ 2 /
          Complex.exp (-((t : ℂ) * Complex.I)) ^ 2 =
        Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, div_eq_mul_inv,
      ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    dsimp only [p]
    push_cast
    ring
  have hfactor (t : ℝ) :
      (-((k : ℂ) / 2) *
          Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) /
          star (zcircle t)) ^ 2 =
        ((p ^ 2 * a ^ 2 / r ^ 2 : ℝ) : ℂ) *
          Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (((k : ℂ) / 2) ^ 2 *
            Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2) /
          star (zcircle t) ^ 2 := by ring
      _ = ((p : ℂ) ^ 2 *
            Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2) /
          star (zcircle t) ^ 2 := by rw [hpCast]
      _ = ((p : ℂ) ^ 2 * w t ^ 2) / star (zcircle t) ^ 2 := by rw [hwsq]
      _ = ((p ^ 2 * a ^ 2 / r ^ 2 : ℝ) : ℂ) *
          (Complex.exp (((p * t : ℝ) : ℂ) * Complex.I) ^ 2 /
            Complex.exp (-((t : ℂ) * Complex.I)) ^ 2) := by
        dsimp only [w]
        rw [hstar, mul_pow, mul_pow]
        push_cast
        field_simp [hr.ne']
      _ = _ := by rw [hphaseFactor]
  have hLeq (t : ℝ) : L t = counterexampleHessianLeading k (zcircle t) := by
    simp only [counterexampleHessianLeading]
    rw [hzNorm, ← hmodel, hfactor]
    dsimp only [L, S]
    push_cast
    ring
  have hLcont : Continuous L := by
    have hmodelCont : Continuous seedTraceFreeHessianModel := by
      unfold seedTraceFreeHessianModel
      fun_prop
    have hwcont : Continuous w := by
      dsimp only [w]
      fun_prop
    have hphaseCont : Continuous (fun t : ℝ ↦
        Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact (continuous_const.mul hphaseCont).mul
      (continuous_star.comp (hmodelCont.comp hwcont))
  have hLnorm (t : ℝ) : ‖L t‖ = S * ‖seedTraceFreeHessianModel (w t)‖ := by
    dsimp only [L]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS,
      Complex.norm_exp, norm_star]
    simp [Complex.mul_re]
  have hzperiod : zcircle (2 * Real.pi) = zcircle 0 := by
    dsimp only [zcircle]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  have hLperiod : L (2 * Real.pi) = L 0 := by
    rw [hLeq, hLeq, hzperiod]
  rcases exists_seed_leading_argument k a 0 with ⟨θ, hθcont, hθphase, hθchange⟩
  refine ⟨L, hLcont, fun t ↦ by simpa only [zcircle] using hLeq t,
    hLperiod, θ, hθcont, ?_, hθchange⟩
  intro t
  have hphase : Complex.exp ((θ t : ℂ) * Complex.I) =
      Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        star (seedTraceFreeHessianModel (w t)) /
          ‖seedTraceFreeHessianModel (w t)‖ := by
    simpa [w, p] using hθphase t
  rw [hphase, hLnorm]
  dsimp only [L]
  push_cast
  field_simp [hS.ne']

/-- Flatness at the origin makes the trace-free Hessian vanish there. -/
@[category research solved, AMS 26 53]
theorem counterexample_traceFreeHessian_zero (k : ℕ) (hk : 0 < k) :
    traceFreeHessian (counterexample k) 0 = 0 := by
  exact traceFreeHessian_eq_zero_of_second_fderiv_eq_zero _ _
    (counterexample_fderiv_fderiv_zero k hk)

/-- The leading oscillatory Hessian term dominates on a punctured neighbourhood of the origin. -/
@[category research solved, AMS 26 53 57]
theorem counterexample_traceFreeHessian_isolated (k : ℕ) (hk : 0 < k) :
    ∃ ε > 0, ∀ w, w ≠ 0 → dist w 0 < ε →
      traceFreeHessian (counterexample k) w ≠ 0 := by
  have hdom := counterexampleHessianError_lt_leading_eventually k hk
  have hnonzero : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      traceFreeHessian (counterexample k) z ≠ 0 := by
    filter_upwards [hdom, self_mem_nhdsWithin] with z hsmall hz
    have hz' : z ≠ 0 := by simpa using hz
    rw [counterexample_traceFreeHessian_decomposition k hz']
    intro hzero
    have heq : counterexampleHessianLeading k z = -counterexampleHessianError k z :=
      eq_neg_of_add_eq_zero_left hzero
    have hnormeq : ‖counterexampleHessianLeading k z‖ =
        ‖counterexampleHessianError k z‖ := by rw [heq, norm_neg]
    exact (ne_of_gt hsmall) hnormeq
  rw [eventually_nhdsWithin_iff] at hnonzero
  rcases Metric.eventually_nhds_iff.mp hnonzero with ⟨ε, hε, hεprop⟩
  refine ⟨ε, hε, fun w hw hdist ↦ ?_⟩
  exact hεprop hdist (by simpa using hw)

/-- On an arbitrarily small positively oriented circle, the trace-free Hessian has an argument
lift whose total change is `2π(2+k)`. -/
@[category research solved, AMS 26 53 57]
theorem counterexample_traceFreeHessian_argument (k : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        traceFreeHessian (counterexample k) (r * Complex.exp ((t : ℂ) * Complex.I)) /
          ‖traceFreeHessian (counterexample k)
            (r * Complex.exp ((t : ℂ) * Complex.I))‖) ∧
      θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  have hdom := counterexampleHessianError_lt_leading_eventually k hk
  rw [eventually_nhdsWithin_iff] at hdom
  rcases Metric.eventually_nhds_iff.mp hdom with ⟨δ, hδ, hδprop⟩
  let r := min (ε / 2) (δ / 2)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  let circle : ℝ → ℂ := fun t ↦
    (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  have hcircleNorm (t : ℝ) : ‖circle t‖ = r := by
    dsimp only [circle]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
    simp [Complex.mul_re]
  have hcircleNe (t : ℝ) : circle t ≠ 0 := by
    rw [← norm_pos_iff, hcircleNorm]
    exact hr
  have hcircleDist (t : ℝ) : dist (circle t) 0 = r := by
    rw [dist_zero_right, hcircleNorm]
  have hcirclePeriod : circle (2 * Real.pi) = circle 0 := by
    dsimp only [circle]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  rcases exists_continuous_counterexampleHessianLeading_circle k hk hr with
    ⟨L, hLcont, hLeq, hLperiod, θ0, hθ0cont, hθ0phase, hθ0change⟩
  let q : ℝ → ℂ := fun t ↦ traceFreeHessian (counterexample k) (circle t)
  let error : ℝ → ℂ := fun t ↦ q t - L t
  have hcircleCont : Continuous circle := by
    dsimp only [circle]
    fun_prop
  have hqcont : Continuous q :=
    (continuous_traceFreeHessian_counterexample k hk).comp hcircleCont
  have herrorcont : Continuous error := hqcont.sub hLcont
  have herrorEq (t : ℝ) : error t = counterexampleHessianError k (circle t) := by
    dsimp only [error, q]
    rw [counterexample_traceFreeHessian_decomposition k (hcircleNe t), ← hLeq]
    ring
  have hsmall (t : ℝ) : ‖error t‖ < ‖L t‖ := by
    rw [herrorEq, hLeq]
    exact hδprop (by simpa only [hcircleDist] using hrδ) (by simpa using hcircleNe t)
  have hqperiod : q (2 * Real.pi) = q 0 := by
    dsimp only [q]
    rw [hcirclePeriod]
  have herrorperiod : error (2 * Real.pi) = error 0 := by
    dsimp only [error]
    rw [hqperiod, hLperiod]
  have hC : Circle.exp (2 * Real.pi * ((2 + k : ℕ) : ℤ)) = 1 :=
    Circle.exp_two_pi_mul_int ((2 + k : ℕ) : ℤ)
  rcases exists_argument_of_norm_error_lt L error (2 * Real.pi)
      (2 * Real.pi * ((2 + k : ℕ) : ℤ)) hLcont herrorcont hsmall hLperiod
      herrorperiod θ0 hθ0cont hθ0phase hθ0change hC with
    ⟨θ, hθcont, hθphase, hθchange⟩
  refine ⟨r, hr, hrε, θ, hθcont, ?_, hθchange⟩
  intro t
  have hsum : L t + error t = q t := by
    dsimp only [error]
    ring
  have hphase := hθphase t
  rw [hsum] at hphase
  simpa only [q, circle] using hphase

/-- For positive `k`, the origin is an isolated umbilic of principal-line index `1 + k / 2`.

`HasIsolatedZeroIndex` stores twice the principal-line index, hence the integer `2 + k` here. -/
@[category research solved, AMS 26 53 57]
theorem counterexample_hasIsolatedZeroIndex (k : ℕ) (hk : 0 < k) :
    HasIsolatedZeroIndex (traceFreeHessian (counterexample k)) 0 (2 + k) := by
  rcases counterexample_traceFreeHessian_isolated k hk with ⟨ε, hε, hisolated⟩
  refine ⟨ε, hε, counterexample_traceFreeHessian_zero k hk, hisolated, ?_⟩
  simpa using counterexample_traceFreeHessian_argument k hk ε hε

/-- Every positive member with `k > 0` violates the index bound in the smooth Loewner
conjecture. -/
@[category research solved, AMS 53 57]
theorem counterexample_not_loewner_bound (k : ℕ) (hk : 0 < k) :
    ¬ ((2 + k : ℕ) : ℤ) ≤ 2 := by
  omega

end CaratheodoryLoewnerCounterexample
