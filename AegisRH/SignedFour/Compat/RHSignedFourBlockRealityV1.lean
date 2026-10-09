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

import RHFourBlockConcreteV3
import Mathlib.Tactic

/-!
AEGIS Ω — signed four-block reality / Toeplitz preflight V1.

This is the first hard gate for RH_SIGNED_FOUR_BLOCK_V1.

The existing four-block coercivity proof replaces each complex cross term by
its norm.  The signed route must retain the actual B entries.  For the
canonical fine packet, the underlying packet is real-valued and every dyadic
translate uses only real scaling and a real argument change.

This module attempts to prove, inside Lean, that:

* real-valued repository packets have real-valued mixed correlation;
* the explicit-formula RHS of a real-valued function is real;
* hence B(a,b) is real for real-valued a,b;
* all dyadic translates of gFine remain real-valued;
* B on the translated gFine family depends only on the translation gap.

If kernel replay accepts these statements, the signed 4×4 Hermitian
compression reduces to a real-symmetric Toeplitz matrix before any
Schur/inertia computation.

No positivity, global Weil sign, or RH conclusion is asserted.

AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Complex
open scoped ComplexConjugate BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSignedFourBlockRealityV1

open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHFourBlockPrimeEightV3
open AEGIS.RHFineMomentPacketV3

def RealValuedFnV1 (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, conj (f x) = f x

def RealValuedPacketV1 (g : WeilCompactSmoothGV1) : Prop :=
  RealValuedFnV1 g.1

theorem gFine_real_v1 : RealValuedPacketV1 gFine := by
  intro x
  simp [gFine, finePacketFn]

theorem translate_real_v1
    (g : WeilCompactSmoothGV1) (hg : RealValuedPacketV1 g) (d : ℝ) :
    RealValuedPacketV1 (translatePacket g d) := by
  intro x
  rw [translatePacket_apply]
  simp only [map_mul, Complex.conj_ofReal]
  rw [hg]

theorem mixed_real_v1
    (a b : WeilCompactSmoothGV1)
    (ha : RealValuedPacketV1 a) (hb : RealValuedPacketV1 b) :
    RealValuedFnV1 (mixed a b) := by
  intro x
  unfold mixed
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have ha' := ha (x * y)
  have hb' := hb y
  simp [Complex.star_def, ha', hb']

theorem primeTerm_real_v1
    (f : ℝ → ℂ) (hf : RealValuedFnV1 f) (n : ℕ) :
    conj (WeilPrimeTermV1 f n) = WeilPrimeTermV1 f n := by
  have hpos := hf ((n : ℝ) + 1)
  have hinv := hf (((n : ℝ) + 1)⁻¹)
  simpa [WeilPrimeTermV1, hpos, hinv]

theorem primeSum_real_v1
    (f : ℝ → ℂ) (hf : RealValuedFnV1 f) :
    conj (WeilPrimeSumV1 f) = WeilPrimeSumV1 f := by
  unfold WeilPrimeSumV1
  change star (∑' n : ℕ, WeilPrimeTermV1 f n) =
    ∑' n : ℕ, WeilPrimeTermV1 f n
  rw [tsum_star]
  apply tsum_congr
  intro n
  exact primeTerm_real_v1 f hf n

theorem archIntegrand_real_v1
    (f : ℝ → ℂ) (hf : RealValuedFnV1 f) (x : ℝ) :
    conj (WeilArchimedeanIntegrandV1 f x) =
      WeilArchimedeanIntegrandV1 f x := by
  have hx := hf x
  have hinv := hf x⁻¹
  have hone := hf 1
  have htwo : conj (2 : ℂ) = (2 : ℂ) := by
    simp only [map_ofNat]
  simpa [WeilArchimedeanIntegrandV1, hx, hinv, hone, htwo]

theorem archIntegral_real_v1
    (f : ℝ → ℂ) (hf : RealValuedFnV1 f) :
    conj (WeilArchimedeanIntegralV1 f) =
      WeilArchimedeanIntegralV1 f := by
  unfold WeilArchimedeanIntegralV1
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact archIntegrand_real_v1 f hf x

theorem explicitRightSide_real_v1
    (f : ℝ → ℂ) (hf : RealValuedFnV1 f) :
    conj (WeilExplicitRightSideV1 f) =
      WeilExplicitRightSideV1 f := by
  unfold WeilExplicitRightSideV1
  have hconst : conj WeilArchimedeanConstantV1 = WeilArchimedeanConstantV1 := by
    simp [WeilArchimedeanConstantV1]
  rw [map_add, map_add, primeSum_real_v1 f hf,
    map_mul, hconst, hf 1, archIntegral_real_v1 f hf]

theorem B_real_of_real_packets_v1
    (a b : WeilCompactSmoothGV1)
    (ha : RealValuedPacketV1 a) (hb : RealValuedPacketV1 b) :
    conj (B a b) = B a b := by
  unfold B
  exact explicitRightSide_real_v1 (mixed a b)
    (mixed_real_v1 a b ha hb)

theorem B_im_zero_of_real_packets_v1
    (a b : WeilCompactSmoothGV1)
    (ha : RealValuedPacketV1 a) (hb : RealValuedPacketV1 b) :
    (B a b).im = 0 := by
  have h := congrArg Complex.im (B_real_of_real_packets_v1 a b ha hb)
  simp only [Complex.conj_im] at h
  linarith

theorem gFine_translate_real_v1 (d : ℝ) :
    RealValuedPacketV1 (translatePacket gFine d) :=
  translate_real_v1 gFine gFine_real_v1 d

theorem gFine_B_real_v1 (d1 d2 : ℝ) :
    conj (B (translatePacket gFine d1) (translatePacket gFine d2)) =
      B (translatePacket gFine d1) (translatePacket gFine d2) :=
  B_real_of_real_packets_v1
    (translatePacket gFine d1) (translatePacket gFine d2)
    (gFine_translate_real_v1 d1) (gFine_translate_real_v1 d2)

theorem gFine_B_im_zero_v1 (d1 d2 : ℝ) :
    (B (translatePacket gFine d1) (translatePacket gFine d2)).im = 0 :=
  B_im_zero_of_real_packets_v1
    (translatePacket gFine d1) (translatePacket gFine d2)
    (gFine_translate_real_v1 d1) (gFine_translate_real_v1 d2)

theorem gFine_B_gap_v1 (d1 d2 : ℝ) :
    B (translatePacket gFine d1) (translatePacket gFine d2) =
      B (translatePacket gFine 0) (translatePacket gFine (d2 - d1)) := by
  apply B_translate_eq_of_gap_v3
  ring

def bGapV1 (d : ℝ) : ℝ :=
  (B (translatePacket gFine 0) (translatePacket gFine d)).re

theorem gFine_B_eq_real_gap_v1 (d1 d2 : ℝ) :
    B (translatePacket gFine d1) (translatePacket gFine d2) =
      (bGapV1 (d2 - d1) : ℂ) := by
  rw [gFine_B_gap_v1]
  apply Complex.ext
  · rfl
  · simp [bGapV1, gFine_B_im_zero_v1]

theorem dyadic_B_toeplitz_v1 (i j : ℕ) :
    B (translatePacket gFine ((i : ℝ) * Real.log 2))
      (translatePacket gFine ((j : ℝ) * Real.log 2)) =
    (bGapV1 (((j : ℝ) - (i : ℝ)) * Real.log 2) : ℂ) := by
  rw [gFine_B_eq_real_gap_v1]
  congr 2
  push_cast
  ring

end AEGIS.RHSignedFourBlockRealityV1

#print axioms AEGIS.RHSignedFourBlockRealityV1.gFine_real_v1
#print axioms AEGIS.RHSignedFourBlockRealityV1.mixed_real_v1
#print axioms AEGIS.RHSignedFourBlockRealityV1.explicitRightSide_real_v1
#print axioms AEGIS.RHSignedFourBlockRealityV1.B_real_of_real_packets_v1
#print axioms AEGIS.RHSignedFourBlockRealityV1.gFine_B_eq_real_gap_v1
#print axioms AEGIS.RHSignedFourBlockRealityV1.dyadic_B_toeplitz_v1
