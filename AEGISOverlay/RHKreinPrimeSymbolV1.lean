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

import RHKreinSymbolIntegrationV1
import RHDyadicDiagonalV13
import WeilThreeBlockPrimeEvaluationV30

/-!
# Prime cosine and the actual finite-window Weil symbol

This module uses the actual paired Mellin inversion theorem and the actual
prime sum. Its window hypothesis is full logarithmic width below log 3.
The symbol convention is angular frequency with Mathlib frequency -t/(2*pi).
-/

open Set Filter MeasureTheory Complex FourierTransform
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinPrimeSymbolV1

open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilFixedLineGammaCoreV10
open AEGIS.WeilDisjointEnergyV2

/-- For full width below log 3, every possible nonzero prime term other than 2
is outside the autocorrelation support. -/
theorem prime_sum_eq_two_of_halfWidth
    (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3) :
    WeilPrimeSumV1 (WeilAutocorrelationV1 g) =
      WeilPrimeTermV1 (WeilAutocorrelationV1 g) 1 := by
  unfold WeilPrimeSumV1
  apply tsum_eq_single 1
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0, WeilPrimeTermV1]
  have hm3R : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hmpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log 3 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hm3R
  have hA : WeilAutocorrelationV1 g ((n + 1 : ℕ) : ℝ) = 0 := by
    have h := autocorrelation_zero_of_halfWidth g r a
      (Real.log ((n + 1 : ℕ) : ℝ)) hw (by linarith)
    rwa [Real.exp_log hmpos] at h
  have hAi : WeilAutocorrelationV1 g (((n + 1 : ℕ) : ℝ))⁻¹ = 0 := by
    rw [weil_autocorrelation_reciprocal_v1 g hmpos, hA]
    simp
  simp only [WeilPrimeTermV1, hA, hAi, mul_zero, add_zero]

theorem criticalSpectralMass_integrable (g : WeilCompactSmoothGV1) :
    Integrable (criticalSpectralMass g) := by
  have h := (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2)).1.re
  simpa only [paired_autocorrelation_eq_criticalSpectralMass,
    RCLike.re_to_complex, Complex.ofReal_re] using h

theorem criticalSpectralMass_nonnegative (g : WeilCompactSmoothGV1) (t : ℝ) :
    0 ≤ criticalSpectralMass g t := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem cosine_mass_integrable (g : WeilCompactSmoothGV1) (u : ℝ) :
    Integrable (fun t : ℝ => Real.cos (t * u) * criticalSpectralMass g t) := by
  have hc : Continuous (fun t : ℝ => Real.cos (t * u)) := by fun_prop
  exact (criticalSpectralMass_integrable g).bdd_mul hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * u))

private theorem critical_exp_profile_integrable
    (g : WeilCompactSmoothGV1) (u : ℝ) :
    Integrable (fun t : ℝ =>
      Complex.exp (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))) *
        (criticalSpectralMass g t : ℂ)) := by
  have hH := (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2)).1
  change Integrable (fun t : ℝ =>
    WeilPairedMellinProfileV5 (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) t) at hH
  simp_rw [paired_autocorrelation_eq_criticalSpectralMass] at hH
  have hc : Continuous (fun t : ℝ =>
      Complex.exp (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ)))) := by fun_prop
  have hb : ∀ t : ℝ,
      ‖Complex.exp (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ)))‖ ≤
        Real.exp (-u / 2) := by
    intro t
    rw [Complex.norm_exp]
    have he : (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))).re = -u / 2 := by
      simp
      ring
    rw [he]
  exact hH.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- Real Mellin inversion at exp u, with its exact exponential factor. -/
theorem cosine_mass_inversion (g : WeilCompactSmoothGV1) (u : ℝ) :
    (1 / (2 * Real.pi)) * Real.exp (-u / 2) *
      (∫ t : ℝ, Real.cos (t * u) * criticalSpectralMass g t) =
    (WeilAutocorrelationV1 g (Real.exp u) +
      (Real.exp (-u) : ℂ) * WeilAutocorrelationV1 g (Real.exp (-u))).re := by
  have h := weil_paired_profile_exp_half_integral_expanded_v10
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) (2 * u)
  have hu : (2 * u) / 2 = u := by ring
  rw [hu] at h
  simp_rw [paired_autocorrelation_eq_criticalSpectralMass] at h
  have hr := congrArg Complex.re h
  have hpoint : ∀ t : ℝ,
      (Complex.exp (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))) *
        (criticalSpectralMass g t : ℂ)).re =
      Real.exp (-u / 2) * (Real.cos (t * u) * criticalSpectralMass g t) := by
    intro t
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.exp_re]
    have he : (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))).re = -u / 2 := by
      simp
      ring
    have hi : (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))).im = -(t * u) := by simp
    rw [he, hi, Real.cos_neg]
    ring
  have hreal :
      (∫ t : ℝ, Complex.exp (-((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ))) *
        (criticalSpectralMass g t : ℂ)).re =
      Real.exp (-u / 2) * ∫ t : ℝ, Real.cos (t * u) * criticalSpectralMass g t := by
    have hre := (integral_re (critical_exp_profile_integrable g u)).symm
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    simp_rw [hpoint]
    rw [integral_const_mul]
  have hs : (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hs, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hreal] at hr
  simpa only [WeilAutocorrelationCompactSmoothV1, mul_assoc] using hr

/-- The factor linking the prime-2 coefficient to the explicit numerical symbol. -/
theorem twice_exp_neg_half_log_two : 2 * Real.exp (-Real.log 2 / 2) = Real.sqrt 2 := by
  rw [show -Real.log 2 / 2 = -(Real.log 2 / 2) by ring, Real.exp_neg,
    AEGIS.WeilThreeBlockPrimeEvaluationV30.exp_log_two_half]
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp [hs]
  nlinarith

/-- The actual prime-2 contribution is exactly its cosine Fourier multiplier. -/
theorem prime_two_real_eq_cosine_mass (g : WeilCompactSmoothGV1) :
    (WeilPrimeTermV1 (WeilAutocorrelationV1 g) 1).re =
      (1 / (4 * Real.pi)) * (Real.sqrt 2 * Real.log 2) *
        ∫ t : ℝ, Real.cos (t * Real.log 2) * criticalSpectralMass g t := by
  have h := cosine_mass_inversion g (Real.log 2)
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  norm_num at h
  have hv : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hs := twice_exp_neg_half_log_two
  simp only [WeilPrimeTermV1, show (1 + 1 : ℕ) = 2 from rfl, hv]
  norm_num only [Nat.cast_ofNat, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  norm_num
  rw [← h]
  rw [← hs]
  ring

/-- Exact explicit symbol consumed by the rational certificate. -/
def symbol (t : ℝ) : ℝ :=
  archSymbol t - Real.sqrt 2 * Real.log 2 * Real.cos (t * Real.log 2)

/-- The Archimedean symbol times the actual spectral mass is integrable. -/
theorem archSymbol_mass_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t : ℝ => archSymbol t * criticalSpectralMass g t) := by
  have hI := AEGIS.RHKreinSymbolIntegrationV1.WeilFixedLineCompletedGammaV10.weil_fixed_line_completed_gamma_integrable_v10
    (WeilAutocorrelationCompactSmoothV1 g) (1 / 2) (by norm_num)
  simp_rw [paired_autocorrelation_eq_criticalSpectralMass] at hI
  refine (hI.re.const_mul (2 : ℝ)).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, completed_gamma_critical_real]
  ring

/-- Full exact symbol identity on logarithmic support width below log 3.
Both Fourier masses are retained, so no evenness of the complex packet is assumed. -/
theorem actual_arithmetic_real_eq_symbol_integral
    (g : WeilCompactSmoothGV1) (r a : ℝ)
    (hw : HalfWidthAt g r a) (hr : 2 * r < Real.log 3) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re =
      -(1 / (4 * Real.pi)) *
        ∫ t : ℝ, symbol t * criticalSpectralMass g t := by
  have hsplit : (∫ t : ℝ, symbol t * criticalSpectralMass g t) =
      (∫ t : ℝ, archSymbol t * criticalSpectralMass g t) -
      (Real.sqrt 2 * Real.log 2) *
        ∫ t : ℝ, Real.cos (t * Real.log 2) * criticalSpectralMass g t := by
    have he : (fun t : ℝ => symbol t * criticalSpectralMass g t) =
        (fun t : ℝ => archSymbol t * criticalSpectralMass g t -
          (Real.sqrt 2 * Real.log 2) *
            (Real.cos (t * Real.log 2) * criticalSpectralMass g t)) := by
      funext t
      unfold symbol
      ring
    rw [he]
    rw [integral_sub (archSymbol_mass_integrable g)
      ((cosine_mass_integrable g (Real.log 2)).const_mul (Real.sqrt 2 * Real.log 2)),
      integral_const_mul]
  rw [actual_arithmetic_real_eq_prime_sub_archSymbol,
    prime_sum_eq_two_of_halfWidth g r a hw hr, prime_two_real_eq_cosine_mass,
    hsplit]
  ring

/-- The same spectral mass gives exactly the actual repository packet energy. -/
theorem energy_eq_mass_integral (g : WeilCompactSmoothGV1) :
    energy g.1 = (1 / (4 * Real.pi)) * ∫ t : ℝ, criticalSpectralMass g t := by
  have h := cosine_mass_inversion g 0
  simp only [neg_zero, zero_div, Real.exp_zero, mul_zero, Real.cos_zero,
    one_mul, mul_one, Complex.ofReal_one, Complex.add_re] at h
  rw [AEGIS.WeilDiagonalKernelReductionV21.autocorrelation_one_re_eq_energy] at h
  calc
    energy g.1 = (1 / 2) * ((1 / (2 * Real.pi)) * ∫ t : ℝ, criticalSpectralMass g t) := by linarith
    _ = _ := by ring

end AEGIS.RHKreinPrimeSymbolV1

#print axioms AEGIS.RHKreinPrimeSymbolV1.prime_sum_eq_two_of_halfWidth
#print axioms AEGIS.RHKreinPrimeSymbolV1.cosine_mass_inversion
#print axioms AEGIS.RHKreinPrimeSymbolV1.actual_arithmetic_real_eq_symbol_integral
#print axioms AEGIS.RHKreinPrimeSymbolV1.energy_eq_mass_integral
