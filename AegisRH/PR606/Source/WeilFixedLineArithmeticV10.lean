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

import WeilXiLogDerivDecompositionV10
import WeilPairedZeroEvaluationV9
import WeilPrimeLineIdentityV1
import WeilPrimeSummabilityV1
import WeilPoleTermV1
import WeilFixedLineCompletedGammaV10
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
AEGIS Ω — fixed-line pole and prime assembly V10.

This module closes the two elementary/arithmetic pieces of the normalized
explicit formula against the actual V5 paired Mellin profile.

* Pole contribution:
    I_c[(1/s + 1/(s-1)) H] = M f(0) + M f(1).
* Prime contribution:
    I_c[(zeta'/zeta) H] = - WeilPrimeSumV1 f.

The prime theorem is the existing kernelized von-Mangoldt line identity
applied to the V8 reciprocal-paired test; a finite-support-safe nat reindex
identifies its RHS with the repository's shifted prime-power sum.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineArithmeticV10

open AEGIS.WeilPairedZeroEvaluationV9

/-- Public version of the Cauchy/profile integrability used internally by V9. -/
theorem paired_profile_cauchy_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    Integrable (fun t : ℝ =>
      (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
        WeilPairedMellinProfileV5 f c t) := by
  let k : ℝ → ℂ := fun t =>
    1 / (((c : ℂ) + (t : ℂ) * I) - a)
  let delta : ℝ := c - a.re
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hne : ∀ t : ℝ,
      ((c : ℂ) + (t : ℂ) * I) - a ≠ 0 := by
    intro t h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hkcont : Continuous k := by
    dsimp [k]
    exact continuous_const.div (by fun_prop) hne
  have hkbound : ∀ t : ℝ, ‖k t‖ ≤ 1 / delta := by
    intro t
    have hre :
        delta ≤ (((c : ℂ) + (t : ℂ) * I) - a).re := by
      dsimp [delta]
      simp
    have hnorm :
        delta ≤ ‖((c : ℂ) + (t : ℂ) * I) - a‖ :=
      hre.trans (Complex.re_le_norm _)
    dsimp [k]
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hdelta hnorm
  have hH :=
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  exact hH.bdd_mul hkcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hkbound)

/-- The elementary xi poles evaluate to the two Mellin endpoints. -/
theorem fixed_line_poles_eq_mellin_endpoints_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / ((c : ℂ) + (t : ℂ) * I) +
          1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
          WeilPairedMellinProfileV5 f c t) =
      mellin f.1 0 + mellin f.1 1 := by
  have h0c : (0 : ℂ).re < c := by
    simp
    linarith
  have h1c : (1 : ℂ).re < c := by
    simpa using hc
  have h0i :=
    paired_profile_cauchy_integrable_v10 f c 0 h0c
  have h1i :=
    paired_profile_cauchy_integrable_v10 f c 1 h1c
  have h0 :=
    paired_profile_cauchy_integral_eq_log_tail_v9 f c 0 h0c
  have h1 :=
    paired_profile_cauchy_integral_eq_log_tail_v9 f c 1 h1c
  have hpair :=
    paired_positive_log_tails_eq_mellin_pair_v9 f (0 : ℂ)
  calc
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / ((c : ℂ) + (t : ℂ) * I) +
          1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
          WeilPairedMellinProfileV5 f c t)
      =
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (1 / (((c : ℂ) + (t : ℂ) * I) - 0)) *
            WeilPairedMellinProfileV5 f c t) +
      ((1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ,
          (1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
            WeilPairedMellinProfileV5 f c t) := by
        rw [show
          (fun t : ℝ =>
            (1 / ((c : ℂ) + (t : ℂ) * I) +
              1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
              WeilPairedMellinProfileV5 f c t) =
          (fun t : ℝ =>
            (1 / (((c : ℂ) + (t : ℂ) * I) - 0)) *
              WeilPairedMellinProfileV5 f c t +
            (1 / (((c : ℂ) + (t : ℂ) * I) - 1)) *
              WeilPairedMellinProfileV5 f c t) by
                funext t
                simp [add_mul]]
        rw [integral_add h0i h1i]
        ring
    _ =
      (∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) 0 v) +
      (∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) 1 v) := by
          rw [h0, h1]
    _ = mellin f.1 0 + mellin f.1 1 := by
          simpa using hpair

/-- The raw von-Mangoldt evaluation of the V8 paired test is exactly the
repository's shifted prime-power sum. -/
theorem paired_test_vonMangoldt_tsum_eq_primeSum_v10
    (f : WeilCompactSmoothGV1) :
    (∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (WeilPairedTestV8 f).1 (n : ℝ)) =
      WeilPrimeSumV1 f.1 := by
  let R : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      (WeilPairedTestV8 f).1 (n : ℝ)
  have hshift :
      (fun n : ℕ => R (n + 1)) = WeilPrimeTermV1 f.1 := by
    funext n
    unfold R WeilPrimeTermV1
    rw [weil_paired_test_apply_v8]
    unfold WeilReciprocalFnV8
    push_cast
    ring
  have hsumShift : Summable (fun n : ℕ => R (n + 1)) := by
    rw [hshift]
    exact weil_compact_smooth_prime_summable_v1 f
  have hsumR : Summable R := by
    exact (summable_nat_add_iff 1).mp hsumShift
  unfold WeilPrimeSumV1
  calc
    (∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        (WeilPairedTestV8 f).1 (n : ℝ))
      = ∑' n : ℕ, R n := by rfl
    _ = R 0 + ∑' n : ℕ, R (n + 1) := hsumR.tsum_eq_zero_add
    _ = ∑' n : ℕ, R (n + 1) := by
          simp [R]
    _ = ∑' n : ℕ, WeilPrimeTermV1 f.1 n := by
          rw [hshift]

/-- Uniform L1 integrability of the von-Mangoldt fixed-line product against
the paired Mellin profile. -/
theorem fixed_line_neg_zeta_logDeriv_integrable_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    Integrable
      (fun t : ℝ =>
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t) := by
  let a : ℕ → ℂ := fun n =>
    (ArithmeticFunction.vonMangoldt n : ℂ)
  let H : ℝ → ℂ := fun t => WeilPairedMellinProfileV5 f c t
  have ha : LSeriesSummable a (c : ℂ) := by
    dsimp [a]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have hH : Integrable H :=
    (weil_paired_mellin_profile_has_vertical_norm_moments_two_v5 f c).1
  let C : ℝ := ∑' n : ℕ, ‖LSeries.term a (c : ℂ) n‖
  have hC0 : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  have hbound :
      ∀ t : ℝ,
        ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖ ≤ C := by
    intro t
    have hat :
        LSeriesSummable a ((c : ℂ) + (t : ℂ) * I) :=
      LSeriesSummable.of_re_le_re (by simp) ha
    calc
      ‖LSeries a ((c : ℂ) + (t : ℂ) * I)‖
        ≤ ∑' n : ℕ,
          ‖LSeries.term a ((c : ℂ) + (t : ℂ) * I) n‖ :=
            norm_tsum_le_tsum_norm hat.norm
      _ = C := by
        apply tsum_congr
        intro n
        exact lseries_term_vertical_norm_v1 a c t n
  have hmajor : Integrable (fun t : ℝ => C * ‖H t‖) :=
    hH.norm.const_mul C
  have hLmeas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
    have hcont :
        Continuous
          (fun t : ℝ =>
            LSeries a ((c : ℂ) + (t : ℂ) * I)) := by
              unfold LSeries
              refine continuous_tsum (u := fun n => ‖LSeries.term a (c : ℂ) n‖)
                (fun n => ?_) ha.norm (fun n t => ?_)
              · rcases eq_or_ne n 0 with rfl | hn
                · simp only [LSeries.term_zero]
                  exact continuous_const
                · simp only [LSeries.term_of_ne_zero hn]
                  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
                  refine continuous_const.div
                    ((by fun_prop : Continuous fun t : ℝ => (c : ℂ) + (t : ℂ) * I).const_cpow
                      (Or.inl hn')) (fun t => ?_)
                  rw [Complex.cpow_def_of_ne_zero hn']
                  exact Complex.exp_ne_zero _
              · exact (lseries_term_vertical_norm_v1 a c t n).le
    exact hcont.aestronglyMeasurable
  have hprod :
      Integrable
        (fun t : ℝ =>
          LSeries a ((c : ℂ) + (t : ℂ) * I) * H t) := by
    refine hmajor.mono'
      (hLmeas.mul hH.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)
  exact hprod.congr
    (Filter.Eventually.of_forall fun t => by
      have hz :=
        WeilPoleTerm.vonMangoldt_lseries_eq_neg_logDeriv_v1
          (s := (c : ℂ) + (t : ℂ) * I)
          (by simpa using hc)
      dsimp [a, H] at hz ⊢
      rw [hz, neg_div])

/-- The zeta logarithmic-derivative contribution is minus the repository
prime-power sum. -/
theorem fixed_line_zeta_logDeriv_eq_neg_primeSum_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t) =
      -WeilPrimeSumV1 f.1 := by
  have hprime :=
    weil_compact_smooth_prime_line_identity_v1
      (WeilPairedTestV8 f) c hc
  have hsum :=
    paired_test_vonMangoldt_tsum_eq_primeSum_v10 f
  have hnegInt :=
    fixed_line_neg_zeta_logDeriv_integrable_v10 f c hc
  have hsign :
      (∫ t : ℝ,
        (deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t) =
      - ∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [hsign]
  have hprofile :
      ∀ t : ℝ,
        mellin (WeilPairedTestV8 f).1
          ((c : ℂ) + (t : ℂ) * I) =
          WeilPairedMellinProfileV5 f c t :=
    weil_paired_test_fixed_line_profile_v8 f c
  simp_rw [hprofile] at hprime
  change
    (1 / (2 * Real.pi) : ℂ) *
      (-(∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          WeilPairedMellinProfileV5 f c t)) =
      -WeilPrimeSumV1 f.1
  have hp : ((1 / (2 * Real.pi) : ℝ) : ℂ) =
      (1 / (2 * Real.pi) : ℂ) := by norm_num
  rw [← hp, mul_neg, ← Complex.real_smul, hprime, hsum]

end AEGIS.WeilFixedLineArithmeticV10

#print axioms AEGIS.WeilFixedLineArithmeticV10.fixed_line_poles_eq_mellin_endpoints_v10
#print axioms AEGIS.WeilFixedLineArithmeticV10.paired_test_vonMangoldt_tsum_eq_primeSum_v10
#print axioms AEGIS.WeilFixedLineArithmeticV10.fixed_line_neg_zeta_logDeriv_integrable_v10
#print axioms AEGIS.WeilFixedLineArithmeticV10.fixed_line_zeta_logDeriv_eq_neg_primeSum_v10
