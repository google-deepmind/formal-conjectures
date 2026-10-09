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

import WeilReciprocalPairedTestV8
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
AEGIS Ω — paired-zero fixed-line evaluation v9.

This module formalizes Section 3 of WeilPairedHadamardIdentityV1.md on top of
the exact-head GREEN V4–V8 fixed-line chain.

For
  H_f,c(t) = M f(c+it) + M f(1-c-it)
and
  K_rho(c,t) = 1/(c+it-rho) + 1/(c+it-(1-rho)),
the target is

  (1/(2*pi)) * integral K_rho(c,t) * H_f,c(t) dt
    = M f(rho) + M f(1-rho).

The proof uses only already-established repository ingredients:
- whole-line exponential substitution for the Mellin transform;
- V6 fixed-line Cauchy/Laplace kernel evaluation;
- V8 reciprocal paired-test closure and Mellin identity;
- the involutive symmetry of the paired test in logarithmic coordinates.

No zero-series summation, gamma/digamma normalization, whole explicit formula,
arithmetic sign inequality, global Weil positivity, or RH conclusion is
asserted here.

AUTHORITY_EFFECT = NONE
RH = NOT_PROVEN
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilPairedZeroEvaluationV9

/-- Log-coordinate Mellin integrand. -/
def WeilLogMellinIntegrandV9
    (f : WeilCompactSmoothGV1) (a : ℂ) (v : ℝ) : ℂ :=
  Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v)

private theorem exp_real_cpow_sub_one_v9
    (a : ℂ) (v : ℝ) :
    (((Real.exp v : ℝ) : ℂ) *
      (((Real.exp v : ℝ) : ℂ) ^ (a - 1))) =
      Complex.exp (a * (v : ℂ)) := by
  have hx : (((Real.exp v : ℝ) : ℂ) ≠ 0) := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
  rw [Complex.cpow_def_of_ne_zero hx]
  have hlog :
      Complex.log (((Real.exp v : ℝ) : ℂ)) = (v : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp]
  rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

/-- Exact whole-line logarithmic representation of the Mellin transform. -/
theorem mellin_eq_log_integral_v9
    (f : WeilCompactSmoothGV1) (a : ℂ) :
    mellin f.1 a = ∫ v : ℝ, WeilLogMellinIntegrandV9 f a v := by
  unfold mellin
  simp only [smul_eq_mul]
  symm
  calc
    (∫ v : ℝ, WeilLogMellinIntegrandV9 f a v) =
        ∫ v : ℝ,
          Real.exp v •
            ((((Real.exp v : ℝ) : ℂ) ^ (a - 1)) *
              f.1 (Real.exp v)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      unfold WeilLogMellinIntegrandV9
      change
        Complex.exp (a * (v : ℂ)) * f.1 (Real.exp v) =
          ((Real.exp v : ℝ) : ℂ) *
            ((((Real.exp v : ℝ) : ℂ) ^ (a - 1)) *
              f.1 (Real.exp v))
      rw [← mul_assoc, exp_real_cpow_sub_one_v9]
    _ = ∫ x : ℝ in Ioi (0 : ℝ),
          ((x : ℂ) ^ (a - 1)) * f.1 x := by
      have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
        MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
        Real.exp_injective.injOn
        (fun x : ℝ => ((x : ℂ) ^ (a - 1)) * f.1 x)
      rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
      rw [h]
      congr 1
      funext v
      rw [abs_of_pos (Real.exp_pos v)]

/-- Compact positive support makes every log-coordinate Mellin integrand
integrable for every complex exponent. -/
private theorem log_mellin_integrable_v9
    (f : WeilCompactSmoothGV1) (a : ℂ) :
    Integrable (WeilLogMellinIntegrandV9 f a) := by
  let K : Set ℝ := Real.log '' tsupport f.1
  have hK : IsCompact K := by
    apply f.2.2.1.image_of_continuousOn
    exact Real.continuousOn_log.mono (by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (f.2.2.2 hx)
      simpa using hx0)
  have hsupp :
      tsupport (WeilLogMellinIntegrandV9 f a) ⊆ K := by
    apply closure_minimal ?_ hK.isClosed
    intro v hv
    by_contra hvK
    apply hv
    have hf0 : f.1 (Real.exp v) = 0 := by
      by_contra hne
      apply hvK
      exact ⟨Real.exp v, subset_tsupport _ hne, Real.log_exp v⟩
    simp [WeilLogMellinIntegrandV9, hf0]
  have hcompact : HasCompactSupport (WeilLogMellinIntegrandV9 f a) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hfc : Continuous f.1 := f.2.1.continuous
  have hcont : Continuous (WeilLogMellinIntegrandV9 f a) := by
    unfold WeilLogMellinIntegrandV9
    fun_prop
  exact hcont.integrable_of_hasCompactSupport hcompact

/-- The V8 paired test is fixed by reciprocal reflection:
q(e^{-v}) = e^v q(e^v). -/
theorem paired_test_exp_neg_v9
    (f : WeilCompactSmoothGV1) (v : ℝ) :
    (WeilPairedTestV8 f).1 (Real.exp (-v)) =
      ((Real.exp v : ℝ) : ℂ) *
        (WeilPairedTestV8 f).1 (Real.exp v) := by
  change
    f.1 (Real.exp (-v)) +
        (((Real.exp (-v))⁻¹ : ℝ) : ℂ) *
          f.1 ((Real.exp (-v))⁻¹) =
      ((Real.exp v : ℝ) : ℂ) *
        (f.1 (Real.exp v) +
          (((Real.exp v)⁻¹ : ℝ) : ℂ) *
            f.1 ((Real.exp v)⁻¹))
  rw [Real.exp_neg, inv_inv]
  push_cast
  have he : Complex.exp (v : ℂ) ≠ 0 := Complex.exp_ne_zero _
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
  ring

/-- Reflection of the paired-test log-Mellin integrand exchanges a with 1-a. -/
theorem paired_log_reflection_v9
    (f : WeilCompactSmoothGV1) (a : ℂ) (v : ℝ) :
    WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a (-v) =
      WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) (1 - a) v := by
  unfold WeilLogMellinIntegrandV9
  rw [paired_test_exp_neg_v9, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The negative half-line for exponent a equals the positive half-line for
the reflected exponent 1-a. -/
theorem paired_log_negative_eq_positive_v9
    (f : WeilCompactSmoothGV1) (a : ℂ) :
    (∫ v : ℝ in Iic (0 : ℝ),
      WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) (1 - a) v := by
  have hneg0 := integral_comp_neg_Ioi
    (0 : ℝ)
    (fun v : ℝ => WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v)
  rw [neg_zero] at hneg0
  rw [← hneg0]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact paired_log_reflection_v9 f a v

/-- The two positive log tails of the reciprocal paired test reconstruct the
full paired Mellin value. -/
theorem paired_positive_log_tails_eq_mellin_pair_v9
    (f : WeilCompactSmoothGV1) (a : ℂ) :
    (∫ v : ℝ in Ioi (0 : ℝ),
      WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v) +
    (∫ v : ℝ in Ioi (0 : ℝ),
      WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) (1 - a) v) =
      mellin f.1 a + mellin f.1 (1 - a) := by
  have hint :=
    log_mellin_integrable_v9 (WeilPairedTestV8 f) a
  have hsplit :=
    intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ))
      (f := WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a)
      hint.integrableOn hint.integrableOn
  have hneg := paired_log_negative_eq_positive_v9 f a
  calc
    (∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v) +
      (∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) (1 - a) v)
        =
      (∫ v : ℝ in Iic (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v) +
      (∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v) := by
          rw [hneg]
          ring
    _ = ∫ v : ℝ,
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v := hsplit
    _ = mellin (WeilPairedTestV8 f).1 a :=
      (mellin_eq_log_integral_v9 (WeilPairedTestV8 f) a).symm
    _ = mellin f.1 a + mellin f.1 (1 - a) :=
      weil_paired_test_mellin_v8 f a

/-- Each single fixed-line Cauchy kernel times the concrete paired Mellin
profile is integrable whenever Re(a)<c. -/
private theorem paired_profile_cauchy_integrable_v9
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

/-- V6 specialized to the V8 paired test and rewritten to the concrete V5
profile. -/
theorem paired_profile_cauchy_integral_eq_log_tail_v9
    (f : WeilCompactSmoothGV1) (c : ℝ) (a : ℂ) (ha : a.re < c) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        (1 / (((c : ℂ) + (t : ℂ) * I) - a)) *
          WeilPairedMellinProfileV5 f c t) =
      ∫ v : ℝ in Ioi (0 : ℝ),
        WeilLogMellinIntegrandV9 (WeilPairedTestV8 f) a v := by
  have h :=
    weil_fixed_line_kernel_integral_log_v6
      (WeilPairedTestV8 f) c a ha
  simpa only [WeilFixedLineMellinV6,
    WeilLogMellinIntegrandV9,
    weil_paired_test_fixed_line_profile_v8] using h

/-- Load-bearing paired-zero evaluation from the mathematical proof note. -/
theorem paired_zero_kernel_integral_evaluation_v9
    (f : WeilCompactSmoothGV1) (c : ℝ) (hc : 1 < c)
    (rho : LiCriterion.NontrivialZero) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        WeilPairedZeroKernelV3 c t rho *
          WeilPairedMellinProfileV5 f c t) =
      mellin f.1 rho.val + mellin f.1 (1 - rho.val) := by
  have hrho : rho.val.re < c :=
    rho.property.2.2.trans hc
  have hone : (1 - rho.val).re < c := by
    simp
    linarith [rho.property.2.1, hc]
  have hint_rho :=
    paired_profile_cauchy_integrable_v9 f c rho.val hrho
  have hint_one :=
    paired_profile_cauchy_integrable_v9 f c (1 - rho.val) hone
  simp_rw [WeilPairedZeroKernelV3, add_mul]
  rw [integral_add hint_rho hint_one, mul_add]
  rw [paired_profile_cauchy_integral_eq_log_tail_v9 f c rho.val hrho]
  rw [paired_profile_cauchy_integral_eq_log_tail_v9 f c (1 - rho.val) hone]
  exact paired_positive_log_tails_eq_mellin_pair_v9 f rho.val

end AEGIS.WeilPairedZeroEvaluationV9

#print axioms AEGIS.WeilPairedZeroEvaluationV9.mellin_eq_log_integral_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_test_exp_neg_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_log_reflection_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_log_negative_eq_positive_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_positive_log_tails_eq_mellin_pair_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_profile_cauchy_integral_eq_log_tail_v9
#print axioms AEGIS.WeilPairedZeroEvaluationV9.paired_zero_kernel_integral_evaluation_v9
