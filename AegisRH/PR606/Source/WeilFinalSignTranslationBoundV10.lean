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

import RHTranslatedKernelDominanceV1
import WeilTranslationGapInvariantV10
import WeilFiniteDilationFilterV10
import WeilOffLineSeedV10
import WeilThreeBlockTranslatedPacketsV22
import Mathlib.Tactic

/-!
AEGIS Ω — final-sign to uniform translated-kernel bound V10.

This module turns the universal final arithmetic sign into a uniform bound on

  d ↦ B(g, T_d g)

for every moment-zero compact-smooth packet g.

The argument is exact:
* translations preserve the two Mellin moments;
* simultaneous translation preserves the diagonal B-value;
* every four-phase two-point combination is again moment-zero;
* FinalSignResidualV1 applied to the four phases gives the exact component box;
* the component box bounds the complex norm uniformly in d.

This is the boundedness input for the Laplace-pole converse.

AUTHORITY_EFFECT = NONE.
-/

open Complex MeasureTheory Set

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFinalSignTranslationBoundV10

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHTranslatedKernelDominanceV1
open AEGIS.WeilTranslationGapInvariantV10
open AEGIS.WeilFiniteDilationFilterV10
open AEGIS.WeilOffLineSeedV10

/-- The repository moment conditions are exactly the two Mellin endpoint
vanishings. -/
theorem momentConditions_iff_mellin_endpoints_v10
    (g : WeilCompactSmoothGV1) :
    WeilMomentConditionsV1 g ↔
      mellin g.1 0 = 0 ∧ mellin g.1 1 = 0 := by
  constructor
  · intro hm
    constructor
    · exact (weil_mellin_zero_eq_moment0_v1 g).trans hm.1
    · exact (weil_mellin_one_eq_moment1_v1 g).trans hm.2
  · rintro ⟨h0, h1⟩
    constructor
    · rw [← weil_mellin_zero_eq_moment0_v1 g]
      exact h0
    · rw [← weil_mellin_one_eq_moment1_v1 g]
      exact h1

theorem momentConditions_scalePacket_v10
    (z : ℂ) (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (scalePacket z g) := by
  rw [momentConditions_iff_mellin_endpoints_v10]
  have hm' := (momentConditions_iff_mellin_endpoints_v10 g).mp hm
  constructor
  · rw [mellin_scalePacket_v10, hm'.1, mul_zero]
  · rw [mellin_scalePacket_v10, hm'.2, mul_zero]

theorem momentConditions_addPacket_v10
    (a b : WeilCompactSmoothGV1)
    (ha : WeilMomentConditionsV1 a)
    (hb : WeilMomentConditionsV1 b) :
    WeilMomentConditionsV1 (addPacket a b) := by
  rw [momentConditions_iff_mellin_endpoints_v10]
  have ha' := (momentConditions_iff_mellin_endpoints_v10 a).mp ha
  have hb' := (momentConditions_iff_mellin_endpoints_v10 b).mp hb
  constructor
  · rw [mellin_addPacket_v10, ha'.1, hb'.1, zero_add]
  · rw [mellin_addPacket_v10, ha'.2, hb'.2, zero_add]

theorem momentConditions_combo_v10
    (z0 z1 z2 : ℂ)
    (g0 g1 g2 : WeilCompactSmoothGV1)
    (h0 : WeilMomentConditionsV1 g0)
    (h1 : WeilMomentConditionsV1 g1)
    (h2 : WeilMomentConditionsV1 g2) :
    WeilMomentConditionsV1
      (combo z0 z1 z2 g0 g1 g2) := by
  unfold combo
  apply momentConditions_addPacket_v10
  · apply momentConditions_addPacket_v10
    · exact momentConditions_scalePacket_v10 z0 g0 h0
    · exact momentConditions_scalePacket_v10 z1 g1 h1
  · exact momentConditions_scalePacket_v10 z2 g2 h2

theorem twoPointPacket_moments_v10
    (g h : WeilCompactSmoothGV1) (c : ℂ)
    (hg : WeilMomentConditionsV1 g)
    (hh : WeilMomentConditionsV1 h) :
    WeilMomentConditionsV1
      (TwoPointPacketV1 g h c) := by
  unfold TwoPointPacketV1
  exact momentConditions_combo_v10
    1 c 0 g h g hg hh hg

/-- Final sign supplies the exact four-phase component box for every translate,
not merely the zero translate. -/
theorem translated_component_bounds_of_final_sign_v10
    (hfinal : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    ArithmeticComponentBoundsV1 g (translatePacket g d) := by
  let h := translatePacket g d
  have hmh : WeilMomentConditionsV1 h := by
    dsimp [h]
    exact translate_preserves_moments g d hm
  have hdiag :
      (B h h).re = (B g g).re := by
    dsimp [h]
    rw [B_translate_diagonal_v10]
  apply
    (weil_four_phase_nonnegative_iff_components_v1
      (ArithmeticDiagonalV1 g)
      (ArithmeticCrossV1 g h)).mp
  intro c hc
  have hm2 :=
    twoPointPacket_moments_v10 g h c hm hmh
  have hs :=
    hfinal (TwoPointPacketV1 g h c) hm2
  have heq :=
    neg_actual_two_point_eq_weil_two_point_v1
      g h c hdiag
  rw [← heq]
  linarith

/-- Direct real/imaginary component bounds on the actual arithmetic cross
term. -/
theorem translated_B_component_bounds_v10
    (hfinal : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    |(B g (translatePacket g d)).re| ≤ -(B g g).re ∧
    |(B g (translatePacket g d)).im| ≤ -(B g g).re := by
  have hb :=
    translated_component_bounds_of_final_sign_v10
      hfinal g hm d
  unfold ArithmeticComponentBoundsV1
    ArithmeticCrossV1 ArithmeticDiagonalV1 at hb
  simpa [abs_neg] using hb

/-- Uniform complex norm bound for the translated arithmetic correlation. -/
theorem translated_B_norm_bound_v10
    (hfinal : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g)
    (d : ℝ) :
    ‖B g (translatePacket g d)‖ ≤
      2 * (-(B g g).re) := by
  obtain ⟨hre, him⟩ :=
    translated_B_component_bounds_v10 hfinal g hm d
  calc
    ‖B g (translatePacket g d)‖
      ≤ |(B g (translatePacket g d)).re| +
          |(B g (translatePacket g d)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * (-(B g g).re) := by linarith

/-- The diagonal orientation required by the bound is automatically
nonnegative under final sign. -/
theorem arithmeticDiagonal_nonnegative_of_final_sign_v10
    (hfinal : AEGIS.RHFinalClosureV1.FinalSignResidualV1)
    (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    0 ≤ -(B g g).re := by
  have hs := hfinal g hm
  change (B g g).re ≤ 0 at hs
  linarith

end AEGIS.WeilFinalSignTranslationBoundV10

#print axioms AEGIS.WeilFinalSignTranslationBoundV10.translated_component_bounds_of_final_sign_v10
#print axioms AEGIS.WeilFinalSignTranslationBoundV10.translated_B_component_bounds_v10
#print axioms AEGIS.WeilFinalSignTranslationBoundV10.translated_B_norm_bound_v10
