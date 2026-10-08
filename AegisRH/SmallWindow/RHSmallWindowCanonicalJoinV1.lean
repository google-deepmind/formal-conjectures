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

import RHSmallWindowProducerV1
import RHWindow693Over2000V1
import RHRestrictedWeilBridgeV13
import Mathlib.Tactic

/-!
AEGIS Ω — canonical finite-window to Weil/RH proof join.

The exact PR #12 radius-1/64 theorem is imported unchanged. The pre-existing
radius-693/2000 theorem covers the smaller radius independently. Exhaustion
and the proved restricted-Weil implication expose the precise large-window
obligation for the original Mathlib RiemannHypothesis proposition.

No global sign hypothesis is silently discharged or asserted as a theorem.
No new axiom, sorry, or weakened definition is introduced.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSmallWindowCanonicalJoinV1

open AEGIS.WeilWindowExhaustionV1
open AEGIS.RHSmallWindowProducerV1
open AEGIS.RHWindow693Over2000V1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHMillenniumGateV10
open AEGIS.RHRestrictedWeilBridgeV13

/-- The stronger existing 693/2000 result contains the 1/64 sign claim. -/
theorem window_one_over_64_of_693_over_2000_v1 :
    WindowArithmeticNonpositiveV1 (1 / 64 : ℝ) :=
  window_le_693_over_2000_arithmetic_nonpositive_v1 (by norm_num)

/-- A proved finite cutoff removes exactly that subinterval from exhaustion. -/
theorem weil_negativity_iff_above_proved_cutoff_v1
    {c : ℝ} (hc : 0 < c) (hcutoff : WindowArithmeticNonpositiveV1 c) :
    WeilCompactSmoothNegativityV1 ↔
      ∀ L : ℝ, c < L → WindowArithmeticNonpositiveV1 L := by
  constructor
  · intro h L hcL
    exact (weil_compact_smooth_negativity_iff_all_windows_v1.mp h) L (hc.trans hcL)
  · intro h
    apply weil_compact_smooth_negativity_iff_all_windows_v1.mpr
    intro L hL
    by_cases hsmall : L ≤ c
    · exact windowArithmeticNonpositive_mono_v1 hsmall hcutoff
    · exact h L (lt_of_not_ge hsmall)

/-- Exhaustion split using the unchanged PR #12 small-window theorem. -/
theorem weil_negativity_iff_above_one_over_64_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ L : ℝ, (1 / 64 : ℝ) < L → WindowArithmeticNonpositiveV1 L :=
  weil_negativity_iff_above_proved_cutoff_v1 (by norm_num)
    windowArithmeticNonpositive_one_over_64_v1

/-- Stronger exhaustion split from the existing near-log-two certificate. -/
theorem weil_negativity_iff_above_693_over_2000_v1 :
    WeilCompactSmoothNegativityV1 ↔
      ∀ L : ℝ, (693 / 2000 : ℝ) < L → WindowArithmeticNonpositiveV1 L :=
  weil_negativity_iff_above_proved_cutoff_v1 (by norm_num)
    window_693_over_2000_arithmetic_nonpositive_v1

/-- The explicit remaining large-window condition produces the real zero quadratic. -/
theorem universal_zero_quadratic_of_above_693_over_2000_v1
    (hLarge : ∀ L : ℝ, (693 / 2000 : ℝ) < L → WindowArithmeticNonpositiveV1 L) :
    UniversalZeroQuadraticNonnegativeV10 := by
  have hNeg : WeilCompactSmoothNegativityV1 :=
    weil_negativity_iff_above_693_over_2000_v1.mpr hLarge
  intro g hm
  have hArithmetic :=
    (weil_compact_smooth_negativity_iff_unconditional_real_inequality_v1.mp hNeg) g hm
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp
    hArithmetic

/-- Official Mathlib RH type, with its unsupplied large-window premise explicit. -/
theorem riemannHypothesis_of_above_693_over_2000_v1
    (hLarge : ∀ L : ℝ, (693 / 2000 : ℝ) < L → WindowArithmeticNonpositiveV1 L) :
    RiemannHypothesis :=
  restricted_weil_criterion_kernel_bridge_v13
    (universal_zero_quadratic_of_above_693_over_2000_v1 hLarge)

end AEGIS.RHSmallWindowCanonicalJoinV1

#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.window_one_over_64_of_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.weil_negativity_iff_above_proved_cutoff_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.weil_negativity_iff_above_one_over_64_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.weil_negativity_iff_above_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.universal_zero_quadratic_of_above_693_over_2000_v1
#print axioms AEGIS.RHSmallWindowCanonicalJoinV1.riemannHypothesis_of_above_693_over_2000_v1
