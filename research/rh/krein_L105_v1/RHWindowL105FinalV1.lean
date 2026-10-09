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

import RHKreinL105AllV1
import RHWindowConnectedL105V1

/-!
# The window `L < 21/40`, unconditional

`RHWindowConnectedL105V1` instantiated with the kernel-checked finite range
(`RHKreinL105AllV1.fcert_finite`, 116 batches) and the tail check.  AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false

namespace AEGIS.RHWindowL105FinalV1

open AEGIS.WeilWindowExhaustionV1

theorem window_lt_21_40 {L : ℝ} (hL0 : 0 ≤ L) (hL : L < 21 / 40) :
    WindowArithmeticNonpositiveV1 L :=
  AEGIS.RHWindowConnectedL105V1.window_lt_21_40
    (fun t h0 h1 => AEGIS.RHKreinL105AllV1.fcert_finite t (by simpa using h0) (by simpa using h1))
    120 256 AEGIS.RHKreinL105AllV1.tail_check hL0 hL

theorem rh_of_windows_from_21_40
    (h : ∀ L : ℝ, 21 / 40 ≤ L → WindowArithmeticNonpositiveV1 L) : RiemannHypothesis :=
  AEGIS.RHWindowConnectedL105V1.rh_of_windows_from_21_40
    (fun t h0 h1 => AEGIS.RHKreinL105AllV1.fcert_finite t (by simpa using h0) (by simpa using h1))
    120 256 AEGIS.RHKreinL105AllV1.tail_check h

end AEGIS.RHWindowL105FinalV1

#print axioms AEGIS.RHWindowL105FinalV1.window_lt_21_40
#print axioms AEGIS.RHWindowL105FinalV1.rh_of_windows_from_21_40
