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

import RHMillenniumGateV10
import WeilAutocorrelationPoleAggregationV1
import WeilThreeBlockTranslatedPacketsV22
import WeilMixedAlgebraV2
import RHTranslatedKernelDominanceV1
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-!
AEGIS Ω — restricted Weil criterion kernel bridge V10, translated-kernel half.

This module formalizes the first load-bearing implication in the mathematical
restricted-Weil proof:

  universal zero-quadratic nonnegativity
    -> four-phase nonnegativity for every real translate
    -> componentwise bounded translated kernel.

The key new identity is exact, not asymptotic:

  Autocorrelation (T_d g) = Autocorrelation g

for the repository translation
  T_d g(x) = exp(-d/2) g(exp(-d) x).

Hence the two translated packets have the same diagonal arithmetic value for
every real d.  Together with linear preservation of the two repository Mellin
moments, the universal sign can be applied to g + c T_d g for each of the four
phases c in {1,-1,i,-i}.  The existing exact four-phase lemma then yields the
component box for every d.

This is the bounded-kernel half of the restricted criterion.  The remaining
transition to RH is the Laplace-pole/off-line-zero contradiction; it is not
asserted in this file.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionKernelBridgeV10

open AEGIS.RHMillenniumGateV10
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHTranslatedKernelDominanceV1

/-- Repository moment conditions are exactly vanishing of the Mellin transform
at the two endpoints 0 and 1. -/
theorem moment_conditions_iff_mellin_endpoints_zero_v10
    (g : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 g ↔
      mellin g.1 0 = 0 ∧ mellin g.1 1 = 0 := by
  constructor
  · intro hm
    exact
      ⟨(weil_mellin_zero_eq_moment0_v1 g).trans hm.1,
       (weil_mellin_one_eq_moment1_v1 g).trans hm.2⟩
  · rintro ⟨h0, h1⟩
    constructor
    · rw [← weil_mellin_zero_eq_moment0_v1 g]
      exact h0
    · rw [← weil_mellin_one_eq_moment1_v1 g]
      exact h1

/-- Complex scaling preserves both zero moments. -/
theorem scalePacket_preserves_moments_v10
    (z : ℂ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (scalePacket z g) := by
  have hg :=
    (moment_conditions_iff_mellin_endpoints_zero_v10 g).mp hm
  apply (moment_conditions_iff_mellin_endpoints_zero_v10
    (scalePacket z g)).mpr
  constructor
  · change mellin (fun x : ℝ => z * g.1 x) 0 = 0
    simpa [smul_eq_mul, hg.1] using
      (mellin_const_smul g.1 (0 : ℂ) z)
  · change mellin (fun x : ℝ => z * g.1 x) 1 = 0
    simpa [smul_eq_mul, hg.2] using
      (mellin_const_smul g.1 (1 : ℂ) z)

/-- Addition preserves both zero moments. -/
theorem addPacket_preserves_moments_v10
    (a b : WeilCompactSmoothGV1)
    (ha : WeilMomentConditionsV1 a)
    (hb : WeilMomentConditionsV1 b) :
    WeilMomentConditionsV1 (addPacket a b) := by
  have ha' :=
    (moment_conditions_iff_mellin_endpoints_zero_v10 a).mp ha
  have hb' :=
    (moment_conditions_iff_mellin_endpoints_zero_v10 b).mp hb
  have ha0 := weil_compact_smooth_mellin_convergent_all_v1 a (0 : ℂ)
  have hb0 := weil_compact_smooth_mellin_convergent_all_v1 b (0 : ℂ)
  have ha1 := weil_compact_smooth_mellin_convergent_all_v1 a (1 : ℂ)
  have hb1 := weil_compact_smooth_mellin_convergent_all_v1 b (1 : ℂ)
  have hadd0 := hasMellin_add ha0 hb0
  have hadd1 := hasMellin_add ha1 hb1
  apply (moment_conditions_iff_mellin_endpoints_zero_v10
    (addPacket a b)).mpr
  constructor
  · change mellin (fun x : ℝ => a.1 x + b.1 x) 0 = 0
    rw [hadd0.2, ha'.1, hb'.1, add_zero]
  · change mellin (fun x : ℝ => a.1 x + b.1 x) 1 = 0
    rw [hadd1.2, ha'.2, hb'.2, add_zero]

/-- The audited three-slot combination preserves the repository moment class
whenever all three inputs do. -/
theorem combo_preserves_moments_v10
    (z0 z1 z2 : ℂ)
    (g0 g1 g2 : WeilCompactSmoothGV1)
    (h0 : WeilMomentConditionsV1 g0)
    (h1 : WeilMomentConditionsV1 g1)
    (h2 : WeilMomentConditionsV1 g2) :
    WeilMomentConditionsV1 (combo z0 z1 z2 g0 g1 g2) := by
  unfold combo
  exact addPacket_preserves_moments_v10
    (addPacket (scalePacket z0 g0) (scalePacket z1 g1))
    (scalePacket z2 g2)
    (addPacket_preserves_moments_v10
      (scalePacket z0 g0) (scalePacket z1 g1)
      (scalePacket_preserves_moments_v10 z0 g0 h0)
      (scalePacket_preserves_moments_v10 z1 g1 h1))
    (scalePacket_preserves_moments_v10 z2 g2 h2)

/-- Every translated two-point packet used by the restricted criterion stays
inside the exact repository moment-zero domain. -/
theorem twoPointPacket_translate_preserves_moments_v10
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) (c : ℂ) :
    WeilMomentConditionsV1
      (TwoPointPacketV1 g (translatePacket g d) c) := by
  unfold TwoPointPacketV1
  exact combo_preserves_moments_v10
    1 c 0 g (translatePacket g d) g
    hm (translate_preserves_moments g d hm) hm

/-- Translation leaves the actual multiplicative autocorrelation unchanged.
The factor exp(-d) from the two packet amplitudes is exactly cancelled by
the Jacobian of y -> exp(-d)y. -/
theorem translate_autocorrelation_eq_v10
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    WeilAutocorrelationV1 (translatePacket g d) =
      WeilAutocorrelationV1 g := by
  funext x
  unfold WeilAutocorrelationV1
  let b : ℝ := Real.exp (-d)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hsubst :=
    integral_comp_mul_left_Ioi'
      (fun u : ℝ => g.1 (x * u) * star (g.1 u))
      0 hb
  simp only [mul_zero] at hsubst
  have hscalar :
      (Real.exp (-d / 2) : ℂ) *
          star (Real.exp (-d / 2) : ℂ) =
        (b : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    norm_cast
    dsimp [b]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (∫ y in Ioi (0 : ℝ),
      (translatePacket g d).1 (x * y) *
        star ((translatePacket g d).1 y))
      =
      (b : ℂ) *
        ∫ y in Ioi (0 : ℝ),
          g.1 (x * (b * y)) * star (g.1 (b * y)) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            simp only [translatePacket_apply]
            have hb' : (b : ℂ) = (Real.exp (-d / 2) : ℂ) * (Real.exp (-d / 2) : ℂ) := by
              rw [← hscalar, Complex.star_def, Complex.conj_ofReal]
            have hxy : x * (b * y) = Real.exp (-d) * (x * y) := by
              dsimp [b]
              ring
            have hy' : b * y = Real.exp (-d) * y := rfl
            rw [hb', hxy, hy']
            simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
            ring
    _ =
      ∫ u in Ioi (0 : ℝ), g.1 (x * u) * star (g.1 u) := by
        simpa [Complex.real_smul, b, mul_assoc] using hsubst

/-- Consequently every real translate has exactly the same diagonal B-value. -/
theorem translate_B_diagonal_eq_v10
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    B (translatePacket g d) (translatePacket g d) = B g g := by
  unfold B
  rw [AEGIS.WeilMixedClosureV2.diagonal_eq,
    AEGIS.WeilMixedClosureV2.diagonal_eq,
    translate_autocorrelation_eq_v10]

/-- Universal zero-quadratic positivity gives actual arithmetic nonpositivity
for every translated two-point test, for every complex coefficient. -/
theorem universal_zero_quadratic_implies_twoPoint_translate_sign_v10
    (hU : UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) (c : ℂ) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1
        (TwoPointPacketV1 g (translatePacket g d) c))).re ≤ 0 := by
  have hFinal :=
    universal_zero_quadratic_iff_final_sign_v10.mp hU
  exact hFinal
    (TwoPointPacketV1 g (translatePacket g d) c)
    (twoPointPacket_translate_preserves_moments_v10 g hm d c)

/-- The universal sign therefore supplies the exact four-phase component box
for every real translate.  This is the formal bounded-kernel statement needed
before the Laplace-pole contradiction. -/
theorem universal_zero_quadratic_implies_translated_component_bounds_v10
    (hU : UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    ArithmeticComponentBoundsV1 g (translatePacket g d) := by
  apply
    (weil_four_phase_nonnegative_iff_components_v1
      (ArithmeticDiagonalV1 g)
      (ArithmeticCrossV1 g (translatePacket g d))).mp
  intro c hc
  have hsign :=
    universal_zero_quadratic_implies_twoPoint_translate_sign_v10
      hU g hm d c
  have hdiag :
      (B (translatePacket g d) (translatePacket g d)).re =
        (B g g).re := by
    rw [translate_B_diagonal_eq_v10]
  have hexact :=
    neg_actual_two_point_eq_weil_two_point_v1
      g (translatePacket g d) c hdiag
  rw [← hexact]
  linarith

/-- Arithmetic translated kernel used by the restricted criterion. -/
def TranslatedArithmeticKernelV10
    (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ArithmeticCrossV1 g (translatePacket g d)

/-- Its diagonal normalization. -/
def TranslatedArithmeticDiagonalV10
    (g : WeilCompactSmoothGV1) : ℝ :=
  ArithmeticDiagonalV1 g

/-- The component box implies a uniform norm bound.  The factor 2 is
deliberately sufficient; the restricted criterion needs boundedness, not the
sharp unit-disc constant. -/
theorem translated_component_bounds_imply_norm_bound_v10
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hb : ArithmeticComponentBoundsV1 g (translatePacket g d)) :
    ‖TranslatedArithmeticKernelV10 g d‖ ≤
      2 * TranslatedArithmeticDiagonalV10 g := by
  rcases hb with ⟨hre, him⟩
  unfold TranslatedArithmeticKernelV10 TranslatedArithmeticDiagonalV10
  calc
    ‖ArithmeticCrossV1 g (translatePacket g d)‖
        ≤ |(ArithmeticCrossV1 g (translatePacket g d)).re| +
            |(ArithmeticCrossV1 g (translatePacket g d)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * ArithmeticDiagonalV1 g := by
      linarith

/-- Universal zero-quadratic positivity therefore makes the translated
arithmetic kernel uniformly bounded on the entire real translation axis. -/
theorem universal_zero_quadratic_implies_translated_kernel_bounded_v10
    (hU : UniversalZeroQuadraticNonnegativeV10)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    ∀ d : ℝ,
      ‖TranslatedArithmeticKernelV10 g d‖ ≤
        2 * TranslatedArithmeticDiagonalV10 g := by
  intro d
  exact translated_component_bounds_imply_norm_bound_v10 g d
    (universal_zero_quadratic_implies_translated_component_bounds_v10
      hU g hm d)

/-- Named universal translated-kernel target produced unconditionally from the
universal zero-quadratic hypothesis. -/
def TranslatedComponentDominanceV10 : Prop :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    ∀ d : ℝ,
      ArithmeticComponentBoundsV1 g (translatePacket g d)

theorem universal_zero_quadratic_implies_translated_component_dominance_v10
    (hU : UniversalZeroQuadraticNonnegativeV10) :
    TranslatedComponentDominanceV10 := by
  intro g hm d
  exact universal_zero_quadratic_implies_translated_component_bounds_v10
    hU g hm d

end AEGIS.RestrictedWeilCriterionKernelBridgeV10

#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.moment_conditions_iff_mellin_endpoints_zero_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.combo_preserves_moments_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.translate_autocorrelation_eq_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.translate_B_diagonal_eq_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.universal_zero_quadratic_implies_translated_component_bounds_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.universal_zero_quadratic_implies_translated_kernel_bounded_v10
#print axioms AEGIS.RestrictedWeilCriterionKernelBridgeV10.universal_zero_quadratic_implies_translated_component_dominance_v10
