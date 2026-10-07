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

import Mathlib
import AEGISOverlay.RHKreinFiniteIntervalKernelV1

open Real
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 100000000

namespace AEGIS.RHEulerGammaSharpBaseV1

open AEGIS.RHKreinFiniteIntervalKernelV1

theorem harmonic_8192_upper :
    harmonic 8192 < (95881900461 / 10000000000 : ℚ) := by
  simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem log_8192 : Real.log 8192 = 13 * Real.log 2 := by
  rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
  norm_num

/-- A sharper rational upper enclosure for Euler's constant, obtained from
the monotone harmonic/log sandwich at `n = 8192`. -/
theorem gamma_lt_5773 :
    Real.eulerMascheroniConstant < (5773 / 10000 : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 8192
  simp only [Real.eulerMascheroniSeq', show (8192 : ℕ) ≠ 0 by norm_num,
    if_false] at h
  have hH : (harmonic 8192 : ℝ) < 95881900461 / 10000000000 := by
    have h' := (Rat.cast_lt (K := ℝ)).mpr harmonic_8192_upper
    push_cast at h'
    exact h'
  have hl : Real.log (((8192 : ℕ) : ℝ)) = 13 * Real.log 2 := by
    norm_num
    exact log_8192
  have h2 := (log_two_enclosure).1
  rw [hl] at h
  norm_num at h2 ⊢
  linarith

end AEGIS.RHEulerGammaSharpBaseV1

#print axioms AEGIS.RHEulerGammaSharpBaseV1.gamma_lt_5773
