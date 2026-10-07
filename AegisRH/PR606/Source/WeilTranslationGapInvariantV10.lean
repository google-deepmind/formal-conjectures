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

import WeilThreeBlockCrossPrimeV28
import WeilMixedAlgebraV2
import Mathlib.Tactic

/-!
AEGIS Ω — general translation-gap invariance V10.

The existing translated-kernel machinery implies that the actual mixed
correlation depends only on the relative logarithmic displacement d₂-d₁.
This module promotes that fact to the complete mixed function and therefore
to the actual arithmetic sesquilinear form B.

In particular:
  B(T_d g, T_d g) = B(g,g)
for every real d, with no RH or sign assumption.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilTranslationGapInvariantV10

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockCrossPrimeV28

theorem mixed_zero_of_nonpos_v10
    (p q : WeilCompactSmoothGV1) {x : ℝ} (hx : x ≤ 0) :
    mixed p q x = 0 := by
  unfold mixed
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have hz := packet_eq_zero_of_nonpos p
    (mul_nonpos_of_nonpos_of_nonneg hx hy.le)
  rw [hz, zero_mul]

/-- Equality of translation gaps gives equality of the complete mixed
functions. -/
theorem mixed_translate_eq_of_gap_v10
    (g : WeilCompactSmoothGV1)
    (d1 d2 e1 e2 : ℝ)
    (hgap : d2 - d1 = e2 - e1) :
    mixed (translatePacket g d1) (translatePacket g d2) =
      mixed (translatePacket g e1) (translatePacket g e2) := by
  funext x
  by_cases hx : 0 < x
  · have h1 :=
      exp_half_mul_mixed_translate_v28
        g d1 d2 (Real.log x)
    have h2 :=
      exp_half_mul_mixed_translate_v28
        g e1 e2 (Real.log x)
    rw [Real.exp_log hx] at h1 h2
    have ha :
        Real.log x + d2 - d1 =
          Real.log x + e2 - e1 := by
      linarith
    rw [ha] at h1
    have he :
        (Real.exp (Real.log x / 2) : ℂ) ≠ 0 := by
      simp
    exact mul_left_cancel₀ he (h1.trans h2.symm)
  · rw [mixed_zero_of_nonpos_v10 _ _ (le_of_not_gt hx),
        mixed_zero_of_nonpos_v10 _ _ (le_of_not_gt hx)]

/-- Actual arithmetic B depends only on the translation gap. -/
theorem B_translate_eq_of_gap_v10
    (g : WeilCompactSmoothGV1)
    (d1 d2 e1 e2 : ℝ)
    (hgap : d2 - d1 = e2 - e1) :
    B (translatePacket g d1) (translatePacket g d2) =
      B (translatePacket g e1) (translatePacket g e2) := by
  unfold B
  rw [mixed_translate_eq_of_gap_v10
    g d1 d2 e1 e2 hgap]

/-- Simultaneous translation leaves the actual B-value unchanged. -/
theorem B_translate_common_v10
    (g : WeilCompactSmoothGV1)
    (d1 d2 a : ℝ) :
    B (translatePacket g (d1 + a))
        (translatePacket g (d2 + a)) =
      B (translatePacket g d1)
        (translatePacket g d2) := by
  apply B_translate_eq_of_gap_v10
  ring

/-- In particular, every translated diagonal is exactly the original
diagonal. -/
theorem B_translate_diagonal_v10
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    B (translatePacket g d) (translatePacket g d) =
      B g g := by
  have h :=
    B_translate_eq_of_gap_v10 g d d 0 0 (by ring)
  have h0 : translatePacket g 0 = g := by
    apply Subtype.ext
    funext x
    simp [translatePacket_apply]
  rw [h0] at h
  exact h

end AEGIS.WeilTranslationGapInvariantV10

#print axioms AEGIS.WeilTranslationGapInvariantV10.mixed_translate_eq_of_gap_v10
#print axioms AEGIS.WeilTranslationGapInvariantV10.B_translate_eq_of_gap_v10
#print axioms AEGIS.WeilTranslationGapInvariantV10.B_translate_diagonal_v10
