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

import RHKreinL105BridgeV1
import WeilWindowExhaustionV1
import RHRestrictedWeilBridgeV13
import WeilAutocorrelationExplicitFormulaV10

/-!
# The width-21/20 Krein certificate in the connected window chain

`RHWindowConnectedV13` connects the window `693/2000` (Coxeter hat class) with window
exhaustion and `final_sign_implies_rh_v13`.  This module plugs the Krein certificate of
autocorrelation width `21/20` into the same chain:

* `window_lt_21_40`: every log window `[−L, L]` with `L < 21/40` has the arithmetic sign;
* `rh_of_windows_from_21_40`: RH follows from the sign on the windows `L ≥ 21/40` alone.

Both are stated relative to the finite-range certificate `hfin` (closed by the kernel batches
of `RHKreinL105AllV1`) and the tail check.  The windows `L ≥ 21/40` are not proved here.
AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindowConnectedL105V1

open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.RHRestrictedWeilBridgeV13
open AEGIS.RHKreinL105BridgeV1
open AEGIS.RHKreinL105TailV1
open AEGIS.RHKreinL105CheckerV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHFinalClosureV1

theorem window_lt_21_40
    (hfin : ∀ t : ℝ, 0 ≤ t → t ≤ 3000 → 0 ≤ Fcert t) (P N : ℕ)
    (htail : tailCheck P N 3000 = true)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : L < 21 / 40) :
    WindowArithmeticNonpositiveV1 L := by
  intro g hm hwindow
  have hw : HalfWidthAt g L 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
    (zero_quadratic_nonneg_L105 hfin P N htail g hm L 0 hL0 (by linarith) hw)

theorem rh_of_windows_from_21_40
    (hfin : ∀ t : ℝ, 0 ≤ t → t ≤ 3000 → 0 ≤ Fcert t) (P N : ℕ)
    (htail : tailCheck P N 3000 = true)
    (h : ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L) :
    RiemannHypothesis := by
  refine final_sign_implies_rh_v13 (fun g hm => ?_)
  obtain ⟨L, hL0, hw⟩ := logLift_has_finite_window_v1 g
  rcases lt_or_ge L (21 / 40) with hlt | hge
  · exact window_lt_21_40 hfin P N htail hL0.le hlt g hm hw
  · exact h L hge g hm hw

end AEGIS.RHWindowConnectedL105V1

#print axioms AEGIS.RHWindowConnectedL105V1.window_lt_21_40
#print axioms AEGIS.RHWindowConnectedL105V1.rh_of_windows_from_21_40
