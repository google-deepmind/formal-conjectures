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

import RHHatCoxClass693V13
import WeilWindowExhaustionV1

/-!
# Exact AEGIS near-log-two sign window, in the existing exhaustion carrier

No mathematical hypothesis is added. This adapter consumes the original
universal_on_class theorem at half-width 693/2000 and translates its genuine
zero-side conclusion through the already-proved explicit formula equivalence.
This is an entire symmetric support window, not universal RH globalization.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHWindow693Over2000V1

open AEGIS.RHHatCoxClass693V13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Recover the original 693/2000 class theorem for every moment-zero packet
in this exact full symmetric logarithmic window. -/
theorem window_693_over_2000_arithmetic_nonpositive_v1 :
    WindowArithmeticNonpositiveV1 (693 / 2000) := by
  intro g hm hwindow
  have hw : HalfWidthAt g (693 / 2000) 0 := by
    simpa [HalfWidthAt, LogSupportIn, LogWindowContainsV1] using hwindow
  have hz := (universal_on_class 0) g hw hm
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr hz

/-- Every smaller symmetric log window inherits the existing proved sign. -/
theorem window_le_693_over_2000_arithmetic_nonpositive_v1
    {L : ℝ} (hL : L ≤ 693 / 2000) :
    WindowArithmeticNonpositiveV1 L :=
  windowArithmeticNonpositive_mono_v1 hL
    window_693_over_2000_arithmetic_nonpositive_v1

end AEGIS.RHWindow693Over2000V1

#print axioms AEGIS.RHWindow693Over2000V1.window_693_over_2000_arithmetic_nonpositive_v1
#print axioms AEGIS.RHWindow693Over2000V1.window_le_693_over_2000_arithmetic_nonpositive_v1
