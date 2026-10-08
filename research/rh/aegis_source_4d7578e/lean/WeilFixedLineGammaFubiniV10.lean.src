import WeilFixedLineGammaCoreV10
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
AEGIS Ω — Gauss-kernel fixed-line Fubini closure V10.

For c > 1 this module proves absolute product-integrability of

  gaussIntegrand ((c + it)/2) u * H_c(t)

on R_t × (0,∞)_u, where H_c is the actual V5 paired Mellin profile.

The key global estimate avoids a small/large-u case split.  For u>0,

  1 - exp(-u) >= u/(1+u),

and the existing AEGIS exponential-difference estimate yields

  ‖gaussIntegrand ((c+it)/2) u‖
    <= 2 (1 + |c/2-1| + |t|) (1+u) exp(-m u),

with m=min(1,c/2)>0.

Thus the majorant factors into:
* the existing V5 A0/A1 t-moments;
* the integrable u-profile (1+u) exp(-m u).

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineGammaFubiniV10

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
    apply Complex.ext <;> simp <;> ring
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
    (c t : ℝ) {u : ℝ} (hc : 1 < c) (hu : 0 < u) :
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
    (c : ℝ) (hc : 1 < c) :
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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
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

end AEGIS.WeilFixedLineGammaFubiniV10

#print axioms AEGIS.WeilFixedLineGammaFubiniV10.gauss_fixed_line_norm_le_v10
#print axioms AEGIS.WeilFixedLineGammaFubiniV10.weil_gauss_fixed_line_kernel_integrable_v10
#print axioms AEGIS.WeilFixedLineGammaFubiniV10.weil_gauss_fixed_line_fubini_v10
