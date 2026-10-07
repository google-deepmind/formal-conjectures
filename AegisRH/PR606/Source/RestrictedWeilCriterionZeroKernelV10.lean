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

import RestrictedWeilCriterionKernelBridgeV10
import WeilExplicitFormulaV10
import WeilAutocorrelationPoleAggregationV1
import WeilMixedClosureV2
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
AEGIS Ω — restricted Weil criterion zero-kernel representation V10.

This module identifies the bounded translated arithmetic kernel from
`RestrictedWeilCriterionKernelBridgeV10` with the canonical multiplicity-
weighted zeta zero exponential sum.

The load-bearing exact identity is

  mixed g (T_d g)(x)
    = exp(d/2) * Autocorrelation(g)(exp(d) * x).

Consequently

  M[mixed g (T_d g)](s)
    = exp(d/2) * exp(d)^(-s) * M[Autocorrelation g](s).

For moment-zero g the mixed Mellin endpoints vanish, so the already assembled
whole explicit formula gives

  - B(g,T_d g)
    = sum_rho m_rho exp(d/2) exp(d)^(-rho)
        M[Autocorrelation g](rho).

Universal zero-quadratic positivity therefore makes this exact zero
exponential sum uniformly bounded for every real d.  This is the analytic
input required by the Laplace-pole/off-line-zero contradiction.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionZeroKernelV10

open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.RHMillenniumGateV10
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHTranslatedKernelDominanceV1
open AEGIS.WeilExplicitFormulaV10

/-- Exact x-space relation between the mixed translated correlation and the
ordinary autocorrelation. -/
theorem mixed_translate_eq_scaled_autocorrelation_v10
    (g : WeilCompactSmoothGV1) (d x : ℝ) :
    mixed g (translatePacket g d) x =
      (Real.exp (d / 2) : ℂ) *
        WeilAutocorrelationV1 g (Real.exp d * x) := by
  let a : ℝ := Real.exp d
  let H : ℝ → ℂ := fun y =>
    g.1 (x * y) * conj (g.1 (Real.exp (-d) * y))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hcancel : Real.exp (-d) * a = 1 := by
    dsimp [a]
    rw [← Real.exp_add]
    simp
  have hcomp :
      (fun u : ℝ => H (a * u)) =
        (fun u : ℝ =>
          g.1 ((a * x) * u) * conj (g.1 u)) := by
    funext u
    dsimp [H]
    have harg1 : x * (a * u) = (a * x) * u := by ring
    have harg2 : Real.exp (-d) * (a * u) = u := by
      rw [← mul_assoc, hcancel, one_mul]
    rw [harg1, harg2]
  have hchange :=
    integral_comp_mul_left_Ioi' H 0 ha
  simp only [mul_zero] at hchange
  rw [hcomp] at hchange
  have hchangeC :
      (a : ℂ) *
        (∫ u in Ioi (0 : ℝ),
          g.1 ((a * x) * u) * conj (g.1 u)) =
        ∫ y in Ioi (0 : ℝ), H y := by
    simpa [Complex.real_smul] using hchange
  have hscalar :
      (Real.exp (-d / 2) : ℂ) * (a : ℂ) =
        (Real.exp (d / 2) : ℂ) := by
    norm_cast
    dsimp [a]
    rw [← Real.exp_add]
    congr 1
    ring
  unfold mixed
  change
    (∫ y in Ioi (0 : ℝ),
      g.1 (x * y) *
        star ((Real.exp (-d / 2) : ℂ) *
          g.1 (Real.exp (-d) * y))) = _
  have hintegrand :
      (fun y : ℝ =>
        g.1 (x * y) *
          star ((Real.exp (-d / 2) : ℂ) *
            g.1 (Real.exp (-d) * y))) =
      (fun y : ℝ => (Real.exp (-d / 2) : ℂ) * H y) := by
    funext y
    dsimp [H]
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [hintegrand, integral_const_mul, ← hchangeC, ← mul_assoc, hscalar]
  rfl

/-- Mellin transform of the mixed translated correlation.  The exponential
factor is deliberately retained in positive-real cpow form; no branch choice
for a complex logarithm is introduced. -/
theorem mellin_mixed_translate_v10
    (g : WeilCompactSmoothGV1) (d : ℝ) (s : ℂ) :
    mellin (mixed g (translatePacket g d)) s =
      (Real.exp (d / 2) : ℂ) *
        ((Real.exp d : ℂ) ^ (-s)) *
          mellin (WeilAutocorrelationV1 g) s := by
  have hfun :
      mixed g (translatePacket g d) =
        fun x : ℝ =>
          (Real.exp (d / 2) : ℂ) *
            WeilAutocorrelationV1 g (Real.exp d * x) := by
    funext x
    exact mixed_translate_eq_scaled_autocorrelation_v10 g d x
  rw [hfun]
  have hc :=
    mellin_const_smul
      (fun x : ℝ => WeilAutocorrelationV1 g (Real.exp d * x))
      s (Real.exp (d / 2) : ℂ)
  have hd :=
    mellin_comp_mul_left
      (WeilAutocorrelationV1 g) s (Real.exp_pos d)
  simp only [smul_eq_mul] at hc hd
  rw [hc, hd]
  ring

/-- Both Mellin endpoints of the mixed translate vanish when the original
packet has the repository's two moments. -/
theorem mixed_translate_mellin_endpoints_zero_v10
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    mellin (mixed g (translatePacket g d)) 0 = 0 ∧
    mellin (mixed g (translatePacket g d)) 1 = 0 := by
  have hgm :=
    (moment_conditions_iff_mellin_endpoints_zero_v10 g).mp hm
  have hA0 :
      mellin (WeilAutocorrelationV1 g) 0 = 0 := by
    rw [weil_autocorrelation_mellin_zero_factor_v1 g,
      hgm.1, hgm.2]
    simp
  have hA1 :
      mellin (WeilAutocorrelationV1 g) 1 = 0 := by
    rw [weil_autocorrelation_mellin_one_factor_v1 g,
      hgm.1, hgm.2]
    simp
  constructor
  · rw [mellin_mixed_translate_v10, hA0]
    ring
  · rw [mellin_mixed_translate_v10, hA1]
    ring

/-- Exact explicit-formula specialization for a mixed translated pair. -/
theorem mixed_translate_B_eq_neg_zero_tsum_v10
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    B g (translatePacket g d) =
      - (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1
            (mixed g (translatePacket g d)) rho) := by
  have hEF :=
    weil_compact_smooth_explicit_formula_v1
      (asPacket g (translatePacket g d))
  have hend :=
    mixed_translate_mellin_endpoints_zero_v10 g hm d
  change
    (∑' rho : RiemannNontrivialZeroIndexV2,
      WeilZeroIndexSummandV1
        (mixed g (translatePacket g d)) rho) =
      mellin (mixed g (translatePacket g d)) 0 +
      mellin (mixed g (translatePacket g d)) 1 -
      B g (translatePacket g d) at hEF
  rw [hend.1, hend.2] at hEF
  simp only [zero_add, zero_sub] at hEF
  exact neg_eq_iff_eq_neg.mp hEF.symm

/-- Centered zero exponent used by the restricted Weil criterion. -/
def CenteredZeroExponentV10
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  (1 / 2 : ℂ) - rho.1

/-- The positive-real cpow translation factor is exactly the ordinary complex
exponential of the centered zero. -/
theorem translated_cpow_factor_eq_exp_centered_v10
    (d : ℝ) (rho : RiemannNontrivialZeroIndexV2) :
    (Real.exp (d / 2) : ℂ) *
        ((Real.exp d : ℂ) ^ (-rho.1)) =
      Complex.exp (CenteredZeroExponentV10 rho * (d : ℂ)) := by
  have hbase : (Real.exp d : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero d)
  have hlog :
      Complex.log (Real.exp d : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos d).le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero hbase, hlog, Complex.ofReal_exp,
    ← Complex.exp_add]
  unfold CenteredZeroExponentV10
  congr 1
  push_cast
  ring

/-- One translated zero exponential summand. -/
def TranslatedZeroSummandV10
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (rho : RiemannNontrivialZeroIndexV2) : ℂ :=
  (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
    ((Real.exp (d / 2) : ℂ) *
      ((Real.exp d : ℂ) ^ (-rho.1)) *
      mellin (WeilAutocorrelationV1 g) rho.1)

/-- The translated summand in its centered exponential normal form. -/
theorem translated_zero_summand_eq_centered_exp_v10
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (rho : RiemannNontrivialZeroIndexV2) :
    TranslatedZeroSummandV10 g d rho =
      (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
        (Complex.exp (CenteredZeroExponentV10 rho * (d : ℂ)) *
          mellin (WeilAutocorrelationV1 g) rho.1) := by
  unfold TranslatedZeroSummandV10
  rw [translated_cpow_factor_eq_exp_centered_v10]

/-- Canonical multiplicity-weighted translated zero exponential kernel. -/
def TranslatedZeroKernelV10
    (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    TranslatedZeroSummandV10 g d rho

/-- Centered exponential representation of the whole translated zero kernel. -/
theorem translated_zero_kernel_eq_centered_exp_tsum_v10
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    TranslatedZeroKernelV10 g d =
      ∑' rho : RiemannNontrivialZeroIndexV2,
        (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
          (Complex.exp (CenteredZeroExponentV10 rho * (d : ℂ)) *
            mellin (WeilAutocorrelationV1 g) rho.1) := by
  unfold TranslatedZeroKernelV10
  apply tsum_congr
  intro rho
  exact translated_zero_summand_eq_centered_exp_v10 g d rho

/-- The translated zero kernel is exactly the negative arithmetic mixed form. -/
theorem translated_zero_kernel_eq_neg_B_v10
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    TranslatedZeroKernelV10 g d =
      - B g (translatePacket g d) := by
  have hB := mixed_translate_B_eq_neg_zero_tsum_v10 g hm d
  rw [hB]
  simp only [neg_neg]
  unfold TranslatedZeroKernelV10
  apply tsum_congr
  intro rho
  unfold TranslatedZeroSummandV10 WeilZeroIndexSummandV1
  rw [mellin_mixed_translate_v10]

/-- The norm of the translated zero kernel is the norm of the arithmetic
cross coefficient used by the four-phase component box. -/
theorem norm_translated_zero_kernel_eq_arithmetic_cross_v10
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    ‖TranslatedZeroKernelV10 g d‖ =
      ‖TranslatedArithmeticKernelV10 g d‖ := by
  rw [translated_zero_kernel_eq_neg_B_v10 g hm d]
  unfold TranslatedArithmeticKernelV10 ArithmeticCrossV1
  simp

/-- Universal zero-quadratic positivity makes the exact multiplicity-weighted
zero exponential kernel uniformly bounded on the whole real axis. -/
theorem universal_zero_quadratic_implies_zero_kernel_bounded_v10
    (hU : UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    ∀ d : ℝ,
      ‖TranslatedZeroKernelV10 g d‖ ≤
        2 * TranslatedArithmeticDiagonalV10 g := by
  intro d
  rw [norm_translated_zero_kernel_eq_arithmetic_cross_v10 g hm d]
  exact
    universal_zero_quadratic_implies_translated_kernel_bounded_v10
      hU g hm d

end AEGIS.RestrictedWeilCriterionZeroKernelV10

#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.mixed_translate_eq_scaled_autocorrelation_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.translated_cpow_factor_eq_exp_centered_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.translated_zero_kernel_eq_centered_exp_tsum_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.mellin_mixed_translate_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.mixed_translate_B_eq_neg_zero_tsum_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.translated_zero_kernel_eq_neg_B_v10
#print axioms AEGIS.RestrictedWeilCriterionZeroKernelV10.universal_zero_quadratic_implies_zero_kernel_bounded_v10
