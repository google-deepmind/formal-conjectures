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

import RHThreeCellClassV13
import WeilWindowExhaustionV1

set_option autoImplicit false
noncomputable section
namespace AEGIS.RHWindowSevenOver32V1
open AEGIS.RHThreeCellClassV13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilWindowExhaustionV1

theorem window_seven_over_32_arithmetic_nonpositive_v1 :
    WindowArithmeticNonpositiveV1 (7 / 32) := by
  intro g hm hwindow
  have hw : HalfWidthAt g (7 / 32) 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  have hc := cell_coercive g 0 hw hm
  have hE := energy_nonnegative g.1
  linarith

theorem window_le_seven_over_32_arithmetic_nonpositive_v1
    {L : ℝ} (hL : L ≤ 7 / 32) : WindowArithmeticNonpositiveV1 L :=
  windowArithmeticNonpositive_mono_v1 hL
    window_seven_over_32_arithmetic_nonpositive_v1

end AEGIS.RHWindowSevenOver32V1

#print axioms AEGIS.RHWindowSevenOver32V1.window_seven_over_32_arithmetic_nonpositive_v1
#print axioms AEGIS.RHWindowSevenOver32V1.window_le_seven_over_32_arithmetic_nonpositive_v1
