import WeilFixedLineGammaXSpaceV10
import WeilFixedLineGammaFubiniV10

/-!
AEGIS Ω — completed-gamma fixed-line normalization V10.

This is the repository-native closure of the gamma/digamma term in the
logarithmic derivative of the completed xi function:

  -1/2 log pi + 1/2 psi(s/2).

Using the source-closed Gauss integral, V10 Fubini closure, x-space
normalization, and the existing paired-profile integral at 1, the normalized
fixed-line integral is exactly

  - WeilArchimedeanConstantV1 * f(1)
  - WeilArchimedeanIntegralV1 f.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineCompletedGammaV10

open AEGIS.WeilFixedLineGammaCoreV10
open AEGIS.WeilFixedLineGammaFubiniV10
open AEGIS.WeilFixedLineGammaAssemblyV10
open AEGIS.WeilFixedLineGammaXSpaceV10

local notation "γ" => Real.eulerMascheroniConstant

def WeilCompletedGammaFactorV10 (c t : ℝ) : ℂ :=
  -(((Real.log Real.pi : ℝ) : ℂ) / 2) +
    (1 / 2 : ℂ) *
      Complex.digamma ((((c : ℂ) + (t : ℂ) * I) / 2))

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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
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
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
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

end AEGIS.WeilFixedLineCompletedGammaV10

#print axioms AEGIS.WeilFixedLineCompletedGammaV10.weil_fixed_line_completed_gamma_eq_archimedean_v10
