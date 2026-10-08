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

import WeilWindowExhaustionV1
import RHNarrowDiagonalUpgradeV2
import Mathlib.Tactic

/-!
AEGIS Ω — unconditional finite-window sign producer V1.

The existing V31 three-block theorem is quantified over an arbitrary
width-1/32 base packet. Setting its coefficients to (0,1,0) collapses the
three-block combination to the untranslated base packet itself. Therefore the
same theorem already yields the exact arithmetic sign for every repository
packet whose logarithmic support is contained in [-1/64,1/64].

The narrower V2 diagonal theorem additionally yields a stronger coercive
estimate on [-1/128,1/128].

No RH hypothesis, universal sign premise, supplied PSD matrix or external
certificate is used.

AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSmallWindowProducerV1

open AEGIS.WeilWindowExhaustionV1
open AEGIS.RHNarrowDiagonalUpgradeV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilSeparatedArchBridgeV31

/-- Radius 1/64 is exactly the retained width-1/32 base-packet condition. -/
theorem window_one_over_64_implies_retained_v1
    (g : WeilCompactSmoothGV1)
    (hw : LogWindowContainsV1 g (1 / 64 : ℝ)) :
    WidthOneThirtyTwoAt g 0 := by
  simpa [LogWindowContainsV1, WidthOneThirtyTwoAt, LogSupportIn] using hw

/-- The (0,1,0) three-block combination is exactly the base packet. -/
theorem middle_three_block_eq_base_v1
    (g : WeilCompactSmoothGV1) :
    AEGIS.WeilMixedAlgebraV2.combo 0 1 0
      (gMinus g) (gZero g) (gPlus g) = g := by
  apply Subtype.ext
  funext x
  simp [AEGIS.WeilMixedAlgebraV2.combo,
    AEGIS.WeilMixedAlgebraV2.addPacket,
    AEGIS.WeilMixedAlgebraV2.scalePacket,
    gMinus, gZero, gPlus, translatePacket_apply]

/-- Unconditional sign producer for the full radius-1/64 finite window. -/
theorem windowArithmeticNonpositive_one_over_64_v1 :
    WindowArithmeticNonpositiveV1 (1 / 64 : ℝ) := by
  intro g hm hw
  have hwidth : WidthOneThirtyTwoAt g 0 :=
    window_one_over_64_implies_retained_v1 g hw
  have h :=
    three_block_bound_of_moments g 0 hwidth hm
      (0 : ℂ) (1 : ℂ) (0 : ℂ)
  rw [middle_three_block_eq_base_v1 g] at h
  have hE : 0 ≤ energy g.1 := energy_nonnegative g.1
  nlinarith

/-- Every smaller nonnegative window inherits the same sign result. -/
theorem windowArithmeticNonpositive_of_nonneg_le_one_over_64_v1
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ (1 / 64 : ℝ)) :
    WindowArithmeticNonpositiveV1 L := by
  exact windowArithmeticNonpositive_mono_v1 hL
    windowArithmeticNonpositive_one_over_64_v1

/-- Radius 1/128 additionally satisfies the narrower coercive diagonal bound. -/
theorem window_one_over_128_implies_narrow_v1
    (g : WeilCompactSmoothGV1)
    (hw : LogWindowContainsV1 g (1 / 128 : ℝ)) :
    WidthOneSixtyFourAt g 0 := by
  simpa [LogWindowContainsV1, WidthOneSixtyFourAt, LogSupportIn] using hw

theorem windowArithmeticNonpositive_one_over_128_v1 :
    WindowArithmeticNonpositiveV1 (1 / 128 : ℝ) :=
  windowArithmeticNonpositive_of_nonneg_le_one_over_64_v1
    (by norm_num) (by norm_num)

end AEGIS.RHSmallWindowProducerV1

#print axioms AEGIS.RHSmallWindowProducerV1.window_one_over_64_implies_retained_v1
#print axioms AEGIS.RHSmallWindowProducerV1.middle_three_block_eq_base_v1
#print axioms AEGIS.RHSmallWindowProducerV1.windowArithmeticNonpositive_one_over_64_v1
#print axioms AEGIS.RHSmallWindowProducerV1.windowArithmeticNonpositive_of_nonneg_le_one_over_64_v1
#print axioms AEGIS.RHSmallWindowProducerV1.windowArithmeticNonpositive_one_over_128_v1
