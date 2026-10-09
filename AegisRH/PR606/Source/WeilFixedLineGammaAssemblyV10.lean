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

import WeilFixedLineGammaFubiniV10
import WeilArchimedeanConvergenceV1

/-!
AEGIS Ω — normalized fixed-line gamma assembly V10.

This module evaluates both iterated integrals from
`WeilFixedLineGammaFubiniV10`.

* u-first: Gauss's digamma integral (now sourced from the pinned Mathlib
  trust surface through the new digamma-series completion);
* t-first: the V10 paired-profile Mellin inversion identities.

The result is the exact logarithmic-u representation of the normalized gamma
term.  The remaining child is only the x=exp(u/2) rewrite plus the elementary
constant aggregation into `WeilArchimedeanConstantV1`.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineGammaAssemblyV10

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1
open AEGIS.WeilFixedLineGammaCoreV10
open AEGIS.WeilFixedLineGammaFubiniV10

local notation "γ" => Real.eulerMascheroniConstant

private theorem paired_exp_profile_integrable_v10
    (f : WeilCompactSmoothGV1) (c u : ℝ) :
    Integrable
      (fun t : ℝ =>
        Complex.exp
          (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ))) *
          WeilPairedMellinProfileV5 f c t) := by
  have hH :=
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  let C : ℝ := Real.exp (-(c * (u / 2)))
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hmajor :
      Integrable
        (fun t : ℝ =>
          C * ‖WeilPairedMellinProfileV5 f c t‖) :=
    hH.norm.const_mul C
  have hExpCont :
      Continuous
        (fun t : ℝ =>
          Complex.exp
            (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ)))) := by
    fun_prop
  have hmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.exp
            (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ))) *
            WeilPairedMellinProfileV5 f c t) :=
    hExpCont.aestronglyMeasurable.mul hH.aestronglyMeasurable
  refine hmajor.mono' hmeas (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre :
      (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ))).re =
        -(c * (u / 2)) := by
    simp
  rw [hre]

/-- Evaluate the u-integral first using the newly source-closed Gauss formula. -/
theorem weil_gauss_kernel_inner_u_v10
    (f : WeilCompactSmoothGV1) (c t : ℝ) (hc : 1 < c) :
    (∫ u : ℝ in Ioi (0 : ℝ),
      WeilGaussFixedLineKernelV10 f c (t, u)) =
      (Complex.digamma
          ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
        WeilPairedMellinProfileV5 f c t := by
  have hz :
      0 <
        ((((c : ℂ) + (t : ℂ) * I) / 2)).re := by
    simp
    linarith
  unfold WeilGaussFixedLineKernelV10
  dsimp only
  rw [integral_mul_const]
  rw [← gauss_digamma_integral_v1
    ((((c : ℂ) + (t : ℂ) * I) / 2)) hz]

/-- Evaluate the normalized t-integral of the Gauss kernel at fixed u. -/
theorem weil_gauss_kernel_inner_t_normalized_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) {u : ℝ}
    (hc : 1 < c) (hu : 0 < u) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        WeilGaussFixedLineKernelV10 f c (t, u)) =
      (Complex.exp (-(u : ℂ)) * (2 * f.1 1) -
        (WeilPairedTestV8 f).1 (Real.exp (u / 2))) /
        (1 - Complex.exp (-(u : ℂ))) := by
  let H : ℝ → ℂ := WeilPairedMellinProfileV5 f c
  let E : ℝ → ℂ := fun t =>
    Complex.exp
      (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ)))
  let a : ℂ := Complex.exp (-(u : ℂ))
  let d : ℂ := 1 - Complex.exp (-(u : ℂ))
  have hd : d ≠ 0 := by
    have hlt : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    dsimp [d]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub]
    exact_mod_cast (sub_pos.mpr hlt).ne'
  have hH : Integrable H := by
    exact (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  have hE : Integrable (fun t => E t * H t) := by
    exact paired_exp_profile_integrable_v10 f c u
  have h1 : Integrable (fun t => (a / d) * H t) :=
    hH.const_mul (a / d)
  have h2 : Integrable (fun t => (1 / d) * (E t * H t)) :=
    hE.const_mul (1 / d)
  have hshape :
      (fun t : ℝ => WeilGaussFixedLineKernelV10 f c (t, u)) =
        fun t => (a / d) * H t - (1 / d) * (E t * H t) := by
    funext t
    unfold WeilGaussFixedLineKernelV10 gaussIntegrand
    dsimp only
    have hexp :
        Complex.exp (-((((c : ℂ) + (t : ℂ) * I) / 2)) * (u : ℂ)) = E t := by
      dsimp [E]
      congr 1
      push_cast
      ring
    rw [hexp]
    dsimp [H, a, d]
    field_simp
  rw [hshape, integral_sub h1 h2, integral_const_mul, integral_const_mul]
  have hHnorm :=
    weil_paired_profile_integral_one_v10 f c
  have hEnorm :=
    weil_paired_profile_exp_half_integral_v10 f c u
  rw [← hHnorm, ← hEnorm]
  have hd' : (1 - Complex.exp (-(u : ℂ))) ≠ 0 := hd
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [H, E, a, d]
  field_simp
  congr 2
  funext t
  ring_nf

/-- Fubini plus both inner evaluations: the normalized fixed-line
`ψ+γ` contribution equals the exact u-space paired-test integral. -/
theorem weil_fixed_line_digamma_plus_gamma_log_integral_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (Complex.digamma
          ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
          WeilPairedMellinProfileV5 f c t) =
      ∫ u : ℝ in Ioi (0 : ℝ),
        (Complex.exp (-(u : ℂ)) * (2 * f.1 1) -
          (WeilPairedTestV8 f).1 (Real.exp (u / 2))) /
          (1 - Complex.exp (-(u : ℂ))) := by
  have hfub :=
    weil_gauss_fixed_line_fubini_v10 f c hc
  have hleft :
      (∫ t : ℝ,
        ∫ u : ℝ in Ioi (0 : ℝ),
          WeilGaussFixedLineKernelV10 f c (t, u)) =
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t =>
      weil_gauss_kernel_inner_u_v10 f c t hc)
  rw [hleft] at hfub
  calc
    (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (Complex.digamma
          ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
          WeilPairedMellinProfileV5 f c t
      =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ in Ioi (0 : ℝ),
          ∫ t : ℝ,
            WeilGaussFixedLineKernelV10 f c (t, u) := by
        rw [hfub]
    _ =
      ∫ u : ℝ in Ioi (0 : ℝ),
        (Complex.exp (-(u : ℂ)) * (2 * f.1 1) -
          (WeilPairedTestV8 f).1 (Real.exp (u / 2))) /
          (1 - Complex.exp (-(u : ℂ))) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        rw [mem_Ioi] at hu
        exact weil_gauss_kernel_inner_t_normalized_v10 f c hc hu

end AEGIS.WeilFixedLineGammaAssemblyV10

#print axioms AEGIS.WeilFixedLineGammaAssemblyV10.weil_gauss_kernel_inner_u_v10
#print axioms AEGIS.WeilFixedLineGammaAssemblyV10.weil_gauss_kernel_inner_t_normalized_v10
#print axioms AEGIS.WeilFixedLineGammaAssemblyV10.weil_fixed_line_digamma_plus_gamma_log_integral_v10
