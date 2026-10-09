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

import WeilFixedLineCompletedGammaV10
import WeilAutocorrelationExplicitFormulaV10
import RHKreinCriticalLineBridgeV1

/-!
# Critical-line Archimedean identity for the actual Weil form

The V10 Gauss integral proofs require only a positive real part. This module
extends their stated `1 < c` domain to `0 < c`, using the same integrable
majorant and the same repository paired Mellin profile. It then specializes
to `c = 1/2` and the actual multiplicative autocorrelation. No positivity,
pointwise symbol certificate, or RH conclusion is assumed or asserted.

Source: AEGIS-OMEGA `2c3d041b633147ec97c7ef753aa9d157a47bb9f5`,
`WeilFixedLineGammaFubiniV10`, `WeilFixedLineGammaAssemblyV10`, and
`WeilFixedLineCompletedGammaV10`.
-/

open Set Filter Topology MeasureTheory Complex FourierTransform
open scoped Topology
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaFubiniV10

open AEGIS.WeilDigammaIntegralReductionV1

def WeilGaussFixedLineKernelV10
    (f : WeilCompactSmoothGV1) (c : ℝ) (p : ℝ × ℝ) : ℂ :=
  gaussIntegrand
      ((((c : ℂ) + (p.1 : ℂ) * I) / 2))
      p.2 *
    WeilPairedMellinProfileV5 f c p.1

private theorem one_sub_exp_neg_lower_v10 {u : ℝ} (hu : 0 < u) :
    u / (1 + u) ≤ 1 - Real.exp (-u) := by
  have h1u : 0 < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by
    simpa [add_comm] using Real.add_one_le_exp u
  have hinv : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg]
    simpa [one_div] using one_div_le_one_div_of_le h1u hexp
  calc
    u / (1 + u) = 1 - 1 / (1 + u) := by
      field_simp [h1u.ne']
      ring
    _ ≤ 1 - Real.exp (-u) := sub_le_sub_left hinv 1

private theorem gauss_denominator_norm_lower_v10 {u : ℝ} (hu : 0 < u) :
    u / (1 + u) ≤
      ‖1 - Complex.exp (-(u : ℂ))‖ := by
  have hexplt : Real.exp (-u) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hnorm :
      ‖1 - Complex.exp (-(u : ℂ))‖ =
        1 - Real.exp (-u) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real]
    exact Real.norm_of_nonneg (sub_nonneg.mpr hexplt.le)
  rw [hnorm]
  exact one_sub_exp_neg_lower_v10 hu

private theorem half_line_shift_norm_le_v10 (c t : ℝ) :
    ‖(((c : ℂ) + (t : ℂ) * I) / 2) - 1‖
      ≤ |c / 2 - 1| + |t| := by
  have hsplit :
      (((c : ℂ) + (t : ℂ) * I) / 2) - 1 =
        ((c / 2 - 1 : ℝ) : ℂ) +
          ((t / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hsplit]
  calc
    ‖((c / 2 - 1 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I‖
        ≤ ‖((c / 2 - 1 : ℝ) : ℂ)‖ +
            ‖((t / 2 : ℝ) : ℂ) * I‖ := norm_add_le _ _
    _ = |c / 2 - 1| + |t / 2| := by
        rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ |c / 2 - 1| + |t| := by
        have ht : |t / 2| ≤ |t| := by
          rw [abs_div]
          norm_num
        linarith

/-- Global Gauss-kernel majorant on the fixed line. -/
theorem gauss_fixed_line_norm_le_v10
    (c t : ℝ) {u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    ‖gaussIntegrand
        ((((c : ℂ) + (t : ℂ) * I) / 2)) u‖
      ≤
      2 * (1 + |c / 2 - 1| + |t|) *
        (1 + u) *
        Real.exp (-(min 1 (c / 2) * u)) := by
  let z : ℂ := (((c : ℂ) + (t : ℂ) * I) / 2)
  let m : ℝ := min 1 (c / 2)
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos (by linarith)
  have hzre : z.re = c / 2 := by
    dsimp [z]
    simp
  have hnum :=
    norm_exp_diff_le z hu
  have hzbound :
      1 + ‖z - 1‖ ≤ 1 + |c / 2 - 1| + |t| := by
    dsimp [z]
    linarith [half_line_shift_norm_le_v10 c t]
  have hnum' :
      ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
        ≤
        2 * (1 + |c / 2 - 1| + |t|) *
          u * Real.exp (-(m * u)) := by
    calc
      ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖
          ≤ 2 * (1 + ‖z - 1‖) * u *
              Real.exp (-(min 1 z.re * u)) := hnum
      _ ≤ 2 * (1 + |c / 2 - 1| + |t|) * u *
              Real.exp (-(m * u)) := by
          rw [hzre]
          dsimp [m]
          gcongr
  have hden :=
    gauss_denominator_norm_lower_v10 hu
  have hsmallpos : 0 < u / (1 + u) := by positivity
  have hdenpos :
      0 < ‖1 - Complex.exp (-(u : ℂ))‖ :=
    hsmallpos.trans_le hden
  unfold gaussIntegrand
  rw [norm_div]
  calc
    ‖Complex.exp (-(u : ℂ)) - Complex.exp (-z * u)‖ /
          ‖1 - Complex.exp (-(u : ℂ))‖
        ≤
      (2 * (1 + |c / 2 - 1| + |t|) *
          u * Real.exp (-(m * u))) /
        (u / (1 + u)) := by
          apply div_le_div₀
          · positivity
          · exact hnum'
          · exact hsmallpos
          · exact hden
    _ =
      2 * (1 + |c / 2 - 1| + |t|) *
        (1 + u) * Real.exp (-(m * u)) := by
          field_simp [hu.ne', (by linarith : (1 + u) ≠ 0)]
    _ =
      2 * (1 + |c / 2 - 1| + |t|) *
        (1 + u) *
        Real.exp (-(min 1 (c / 2) * u)) := by rfl

private theorem gamma_u_majorant_integrable_v10
    (c : ℝ) (hc : 0 < c) :
    Integrable
      (fun u : ℝ =>
        (1 + u) * Real.exp (-(min 1 (c / 2) * u)))
      (volume.restrict (Ioi (0 : ℝ))) := by
  let m : ℝ := min 1 (c / 2)
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min one_pos (by linarith)
  have h0 :
      IntegrableOn
        (fun u : ℝ => Real.exp (-m * u))
        (Ioi (0 : ℝ)) := by
    simpa [neg_mul] using
      (integrableOn_exp_mul_Ioi (a := -m) (by linarith) 0)
  have h1 :
      IntegrableOn
        (fun u : ℝ => u * Real.exp (-(m * u)))
        (Ioi (0 : ℝ)) := by
    have hI :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := m)
        (by norm_num) (by norm_num) hm
    refine hI.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  refine (h0.add h1).congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Pi.add_apply, m, neg_mul]
  ring

private theorem gamma_t_majorant_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) :
    Integrable
      (fun t : ℝ =>
        (1 + |c / 2 - 1| + |t|) *
          ‖WeilPairedMellinProfileV5 f c t‖) := by
  have hH :=
    weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c
  let A : ℝ := 1 + |c / 2 - 1|
  have h0 :
      Integrable
        (fun t : ℝ =>
          A * ‖WeilPairedMellinProfileV5 f c t‖) :=
    hH.1.norm.const_mul A
  have h1 :
      Integrable
        (fun t : ℝ =>
          |t| * ‖WeilPairedMellinProfileV5 f c t‖) :=
    hH.2.1
  refine (h0.add h1).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, A]
  ring

/-- Absolute product-integrability of the Gauss kernel against the actual V5
paired Mellin profile. -/
theorem weil_gauss_fixed_line_kernel_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    Integrable
      (WeilGaussFixedLineKernelV10 f c)
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let T : ℝ → ℝ := fun t =>
    (1 + |c / 2 - 1| + |t|) *
      ‖WeilPairedMellinProfileV5 f c t‖
  let U : ℝ → ℝ := fun u =>
    (1 + u) * Real.exp (-(min 1 (c / 2) * u))
  have hT : Integrable T := by
    exact gamma_t_majorant_integrable_v10 f c
  have hU :
      Integrable U (volume.restrict (Ioi (0 : ℝ))) := by
    exact gamma_u_majorant_integrable_v10 c hc
  have hmajor :
      Integrable
        (fun p : ℝ × ℝ => 2 * T p.1 * U p.2)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    exact (hT.const_mul 2).mul_prod hU
  have hmeas :
      AEStronglyMeasurable
        (WeilGaussFixedLineKernelV10 f c)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold WeilGaussFixedLineKernelV10
    have hH :=
      (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
    have hHm :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            WeilPairedMellinProfileV5 f c p.1)
          (volume.prod (volume.restrict (Ioi (0 : ℝ)))) :=
      hH.aestronglyMeasurable.comp_fst
    have hGm :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            gaussIntegrand
              ((((c : ℂ) + (p.1 : ℂ) * I) / 2)) p.2)
          (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      apply Measurable.aestronglyMeasurable
      unfold gaussIntegrand
      fun_prop
    exact hGm.mul hHm
  refine hmajor.mono' hmeas ?_
  have hpos_ae :
      ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))), 0 < p.2 := by
    change ∀ᵐ p : ℝ × ℝ ∂(volume.prod (volume.restrict (Ioi (0 : ℝ)))),
        p ∈ Prod.snd ⁻¹' Ioi (0 : ℝ)
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurable_snd measurableSet_Ioi)]
    exact Filter.Eventually.of_forall (fun _ => by
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun u hu => hu))
  filter_upwards [hpos_ae] with p hp
  have hu : 0 < p.2 := hp
  unfold WeilGaussFixedLineKernelV10
  rw [norm_mul]
  have hg :=
    gauss_fixed_line_norm_le_v10 c p.1 hc hu
  calc
      ‖gaussIntegrand
          ((((c : ℂ) + (p.1 : ℂ) * I) / 2)) p.2‖ *
          ‖WeilPairedMellinProfileV5 f c p.1‖
        ≤
        (2 * (1 + |c / 2 - 1| + |p.1|) *
          (1 + p.2) *
          Real.exp (-(min 1 (c / 2) * p.2))) *
          ‖WeilPairedMellinProfileV5 f c p.1‖ := by
          gcongr
    _ = 2 * T p.1 * U p.2 := by
          simp [T, U]
          ring

/-- The actual Gauss-kernel t/u Fubini swap. -/
theorem weil_gauss_fixed_line_fubini_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ,
      ∫ u : ℝ in Ioi (0 : ℝ),
        WeilGaussFixedLineKernelV10 f c (t, u)) =
      ∫ u : ℝ in Ioi (0 : ℝ),
        ∫ t : ℝ,
          WeilGaussFixedLineKernelV10 f c (t, u) := by
  have hprod :=
    weil_gauss_fixed_line_kernel_integrable_v10 f c hc
  simpa [Function.uncurry_def] using
    (integral_integral_swap
      (μ := volume) (ν := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t u => WeilGaussFixedLineKernelV10 f c (t, u))
      hprod)

end AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaFubiniV10


namespace AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaAssemblyV10

open AEGIS.WeilDigammaIntegralReductionV1
open AEGIS.WeilDigammaSeriesHalfPlaneV1
open AEGIS.WeilFixedLineGammaCoreV10
open AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaFubiniV10

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
    (f : WeilCompactSmoothGV1) (c t : ℝ) (hc : 0 < c) :
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
    (hu : 0 < u) :
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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
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
        exact weil_gauss_kernel_inner_t_normalized_v10 f c hu

end AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaAssemblyV10


namespace AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaXSpaceV10
open AEGIS.WeilFixedLineGammaXSpaceV10
open AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaAssemblyV10
local notation "γ" => Real.eulerMascheroniConstant

theorem half_fixed_line_digamma_plus_gamma_eq_arch_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    (1 / 2 : ℂ) *
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) =
      -WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1 := by
  have hlog :=
    weil_fixed_line_digamma_plus_gamma_log_integral_v10 f c hc
  have hlog' :
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) =
        ∫ u : ℝ in Ioi (0 : ℝ),
          WeilGammaLogIntegrandV10 f u := by
    simpa [WeilGammaLogIntegrandV10] using hlog
  rw [hlog']
  rw [half_gamma_log_integral_eq_x_integral_v10]
  exact gamma_x_integral_eq_arch_v10 f

end AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaXSpaceV10


namespace AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineCompletedGammaV10

open AEGIS.WeilFixedLineGammaCoreV10
open AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaFubiniV10
open AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaAssemblyV10
open AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineGammaXSpaceV10

local notation "γ" => Real.eulerMascheroniConstant

open AEGIS.WeilFixedLineCompletedGammaV10

private theorem log_four_pi_normalization_v10 :
    2 * Real.log 2 + Real.log Real.pi =
      Real.log (4 * Real.pi) := by
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := by
        rw [Real.log_mul] <;> norm_num
      _ = 2 * Real.log 2 := by ring
  calc
    2 * Real.log 2 + Real.log Real.pi
      = Real.log 4 + Real.log Real.pi := by rw [hlog4]
    _ = Real.log (4 * Real.pi) := by
      rw [Real.log_mul] <;> positivity

private theorem digamma_plus_gamma_profile_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    Integrable
      (fun t : ℝ =>
        (Complex.digamma
          ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
          WeilPairedMellinProfileV5 f c t) := by
  have hprod :=
    weil_gauss_fixed_line_kernel_integrable_v10 f c hc
  have hinner :
      Integrable
        (fun t : ℝ =>
          ∫ u : ℝ in Ioi (0 : ℝ),
            WeilGaussFixedLineKernelV10 f c (t, u)) :=
    hprod.integral_prod_left
  exact hinner.congr
    (Filter.Eventually.of_forall fun t =>
      weil_gauss_kernel_inner_u_v10 f c t hc)

private theorem completed_gamma_pointwise_split_v10
    (f : WeilCompactSmoothGV1) (c t : ℝ) :
    WeilCompletedGammaFactorV10 c t *
        WeilPairedMellinProfileV5 f c t =
      (1 / 2 : ℂ) *
        ((Complex.digamma
          ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
          WeilPairedMellinProfileV5 f c t) -
      (1 / 2 : ℂ) *
        (((Real.log Real.pi + γ : ℝ) : ℂ) *
          WeilPairedMellinProfileV5 f c t) := by
  unfold WeilCompletedGammaFactorV10
  push_cast
  ring

/-- Public integrability surface for the completed-gamma contribution.
This exposes an obligation already discharged internally by the Gauss-kernel
product-integrability proof. -/
theorem weil_fixed_line_completed_gamma_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    Integrable
      (fun t : ℝ =>
        WeilCompletedGammaFactorV10 c t *
          WeilPairedMellinProfileV5 f c t) := by
  have hplus :=
    digamma_plus_gamma_profile_integrable_v10 f c hc
  have hH :=
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  have hA :
      Integrable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            ((Complex.digamma
              ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
              WeilPairedMellinProfileV5 f c t)) :=
    hplus.const_mul (1 / 2 : ℂ)
  have hB :
      Integrable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            (((Real.log Real.pi + γ : ℝ) : ℂ) *
              WeilPairedMellinProfileV5 f c t)) := by
    exact
      (hH.const_mul (((Real.log Real.pi + γ : ℝ) : ℂ))).const_mul
        (1 / 2 : ℂ)
  exact (hA.sub hB).congr
    (Filter.Eventually.of_forall fun t =>
      (completed_gamma_pointwise_split_v10 f c t).symm)

/-- Exact repository-native completed-gamma contribution. -/
theorem weil_fixed_line_completed_gamma_eq_archimedean_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        WeilCompletedGammaFactorV10 c t *
          WeilPairedMellinProfileV5 f c t) =
      -WeilArchimedeanConstantV1 * f.1 1 -
        WeilArchimedeanIntegralV1 f.1 := by
  have hplus :=
    digamma_plus_gamma_profile_integrable_v10 f c hc
  have hH :=
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  have hA :
      Integrable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            ((Complex.digamma
              ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
              WeilPairedMellinProfileV5 f c t)) :=
    hplus.const_mul (1 / 2 : ℂ)
  have hB :
      Integrable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            (((Real.log Real.pi + γ : ℝ) : ℂ) *
              WeilPairedMellinProfileV5 f c t)) := by
    exact
      (hH.const_mul (((Real.log Real.pi + γ : ℝ) : ℂ))).const_mul
        (1 / 2 : ℂ)
  have hsplit :
      (∫ t : ℝ,
        WeilCompletedGammaFactorV10 c t *
          WeilPairedMellinProfileV5 f c t) =
      (∫ t : ℝ,
        (1 / 2 : ℂ) *
          ((Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t)) -
      (∫ t : ℝ,
        (1 / 2 : ℂ) *
          (((Real.log Real.pi + γ : ℝ) : ℂ) *
            WeilPairedMellinProfileV5 f c t)) := by
    calc
      (∫ t : ℝ,
        WeilCompletedGammaFactorV10 c t *
          WeilPairedMellinProfileV5 f c t)
        =
      ∫ t : ℝ,
        ((1 / 2 : ℂ) *
          ((Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) -
        (1 / 2 : ℂ) *
          (((Real.log Real.pi + γ : ℝ) : ℂ) *
            WeilPairedMellinProfileV5 f c t)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (fun t => completed_gamma_pointwise_split_v10 f c t)
      _ = _ := integral_sub hA hB
  rw [hsplit, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have hhalf :=
    half_fixed_line_digamma_plus_gamma_eq_arch_v10 f c hc
  have hprofile :=
    weil_paired_profile_integral_one_v10 f c
  have hlognorm := log_four_pi_normalization_v10
  unfold WeilArchimedeanConstantV1
  calc
    (1 / (2 * Real.pi) : ℂ) *
      (((1 / 2 : ℂ) *
        ∫ t : ℝ,
          (Complex.digamma
            ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
            WeilPairedMellinProfileV5 f c t) -
        (1 / 2 : ℂ) *
          (((Real.log Real.pi + γ : ℝ) : ℂ) *
            ∫ t : ℝ, WeilPairedMellinProfileV5 f c t))
      =
      ((1 / 2 : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ,
            (Complex.digamma
              ((((c : ℂ) + (t : ℂ) * I) / 2)) + (γ : ℂ)) *
              WeilPairedMellinProfileV5 f c t)) -
      (1 / 2 : ℂ) *
        (((Real.log Real.pi + γ : ℝ) : ℂ) *
          ((1 / (2 * Real.pi) : ℂ) *
            ∫ t : ℝ, WeilPairedMellinProfileV5 f c t)) := by
          ring
    _ =
      (-WeilArchimedeanIntegralV1 f.1 -
        ((2 * Real.log 2 : ℝ) : ℂ) * f.1 1) -
      (((Real.log Real.pi + γ : ℝ) : ℂ) * f.1 1) := by
          rw [hhalf, hprofile]
          ring
    _ =
      -(((Real.log (4 * Real.pi) + γ : ℝ) : ℂ)) * f.1 1 -
        WeilArchimedeanIntegralV1 f.1 := by
          rw [← hlognorm]
          push_cast
          ring

end AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineCompletedGammaV10

namespace AEGIS.RHKreinSymbolIntegrationV1

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.RHKreinCriticalLineBridgeV1
open AEGIS.WeilFixedLineCompletedGammaV10

/-- The two actual critical-line autocorrelation Mellin values, expressed
using Mathlib's Fourier convention. -/
def criticalSpectralMass (g : WeilCompactSmoothGV1) (t : ℝ) : ℝ :=
  Complex.normSq (𝓕 (logLift g.1) (-t / (2 * Real.pi))) +
    Complex.normSq (𝓕 (logLift g.1) (-(-t) / (2 * Real.pi)))

/-- The Archimedean part of the angular-frequency numerical symbol. -/
def archSymbol (t : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + (t : ℂ) * I / 2)).re - Real.log Real.pi

theorem paired_autocorrelation_eq_criticalSpectralMass
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    WeilPairedMellinProfileV5 (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) t =
      (criticalSpectralMass g t : ℂ) := by
  change mellin (WeilAutocorrelationV1 g) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) +
    mellin (WeilAutocorrelationV1 g)
      (((1 - 1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = _
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
    autocorrelation_mellin_critical_normSq_v1 g t,
    autocorrelation_mellin_critical_normSq_v1 g (-t)]
  simp only [criticalSpectralMass, Complex.ofReal_add]

theorem completed_gamma_critical_real (t : ℝ) :
    (WeilCompletedGammaFactorV10 (1 / 2) t).re = (1 / 2) * archSymbol t := by
  have hz : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) / 2) =
      (1 / 4 : ℂ) + (t : ℂ) * I / 2 := by push_cast; ring
  simp only [WeilCompletedGammaFactorV10, hz, archSymbol]
  simp
  ring

/-- The actual arithmetic form, with its Archimedean part represented on the
critical line. The prime sum is unchanged. -/
theorem actual_arithmetic_eq_prime_sub_critical_gamma
    (g : WeilCompactSmoothGV1) :
    WeilExplicitRightSideV1 (WeilAutocorrelationV1 g) =
      WeilPrimeSumV1 (WeilAutocorrelationV1 g) -
        (1 / (2 * Real.pi) : ℂ) *
          ∫ t : ℝ, WeilCompletedGammaFactorV10 (1 / 2) t *
            (criticalSpectralMass g t : ℂ) := by
  have h := WeilFixedLineCompletedGammaV10.weil_fixed_line_completed_gamma_eq_archimedean_v10
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) (by norm_num)
  simp_rw [paired_autocorrelation_eq_criticalSpectralMass] at h
  change (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, WeilCompletedGammaFactorV10 (1 / 2) t *
        (criticalSpectralMass g t : ℂ)) =
    -WeilArchimedeanConstantV1 * WeilAutocorrelationV1 g 1 -
      WeilArchimedeanIntegralV1 (WeilAutocorrelationV1 g) at h
  rw [h]
  unfold WeilExplicitRightSideV1
  ring

/-- Exact real Archimedean symbol identity for the actual repository form.
The factor `1/(4*pi)` multiplies the sum of both frequency masses. -/
theorem actual_arithmetic_real_eq_prime_sub_archSymbol
    (g : WeilCompactSmoothGV1) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      (WeilPrimeSumV1 (WeilAutocorrelationV1 g)).re -
        (1 / (4 * Real.pi)) *
          ∫ t : ℝ, archSymbol t * criticalSpectralMass g t := by
  have hI := WeilFixedLineCompletedGammaV10.weil_fixed_line_completed_gamma_integrable_v10
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) (by norm_num)
  simp_rw [paired_autocorrelation_eq_criticalSpectralMass] at hI
  have hpoint : ∀ t : ℝ,
      (WeilCompletedGammaFactorV10 (1 / 2) t *
        (criticalSpectralMass g t : ℂ)).re =
      (1 / 2) * (archSymbol t * criticalSpectralMass g t) := by
    intro t
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      completed_gamma_critical_real]
    ring
  have hreal :
      (∫ t : ℝ, WeilCompletedGammaFactorV10 (1 / 2) t *
        (criticalSpectralMass g t : ℂ)).re =
      (1 / 2) * ∫ t : ℝ, archSymbol t * criticalSpectralMass g t := by
    have hre := (integral_re hI).symm
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    simp_rw [hpoint]
    rw [integral_const_mul]
  rw [actual_arithmetic_eq_prime_sub_critical_gamma]
  rw [Complex.sub_re, Complex.mul_re]
  have hscalar : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hscalar, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hreal]
  ring

end AEGIS.RHKreinSymbolIntegrationV1

#print axioms AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineCompletedGammaV10.weil_fixed_line_completed_gamma_eq_archimedean_v10
#print axioms AEGIS.RHKreinSymbolIntegrationV1.actual_arithmetic_eq_prime_sub_critical_gamma
#print axioms AEGIS.RHKreinSymbolIntegrationV1.actual_arithmetic_real_eq_prime_sub_archSymbol
