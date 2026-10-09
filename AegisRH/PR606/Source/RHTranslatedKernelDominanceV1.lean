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

import RHFinalClosureSpineV1
import WeilAbjadFourPhaseBridgeV1
import WeilThreeBlockTranslatedPacketsV22
import WeilMixedAlgebraV2
import Mathlib.Tactic

/-!
AEGIS Ω — translated two-point RKHS/Bombieri composition spine v1.

This module identifies the exact scalar interface between the existing
finite-RKHS/Gram dominance layer and the actual repository arithmetic form.

No RH conclusion is asserted here.

For packets g,h define
  a = -Re B(g,g)
  z = -conj(B(g,h)).
The existing four-phase theorem says the component box
  |Re z| <= a, |Im z| <= a
is exactly the four-phase two-point nonnegativity condition.

At zero translation h = g.  The component box then reduces exactly to
  Re B(g,g) <= 0.
Consequently universal zero-shift component dominance on the moment-zero
class is equivalent to RHFinalClosureV1.FinalSignResidualV1.

This is the formal socket into which an actual-zeta RKHS dominance certificate
must bind.  Generic supplied-matrix dominance by itself is not promoted.
-/

open Set MeasureTheory Complex

set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section

namespace AEGIS.RHTranslatedKernelDominanceV1

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22

/-- Two-point packet written using the already-audited three-block combination
with the third coefficient set to zero. -/
def TwoPointPacketV1
    (g h : WeilCompactSmoothGV1) (c : ℂ) : WeilCompactSmoothGV1 :=
  AEGIS.WeilMixedAlgebraV2.combo 1 c 0 g h g

/-- Positive-or-negative diagonal scalar in the Bombieri orientation. -/
def ArithmeticDiagonalV1 (g : WeilCompactSmoothGV1) : ℝ :=
  -(AEGIS.WeilMixedAlgebraV2.B g g).re

/-- Cross scalar in the orientation expected by WeilTwoPointValueV1. -/
def ArithmeticCrossV1
    (g h : WeilCompactSmoothGV1) : ℂ :=
  -conj (AEGIS.WeilMixedAlgebraV2.B g h)

/-- Exact component-box interface supplied by a two-point RKHS/Gram dominance
certificate. -/
def ArithmeticComponentBoundsV1
    (g h : WeilCompactSmoothGV1) : Prop :=
  |(ArithmeticCrossV1 g h).re| ≤ ArithmeticDiagonalV1 g ∧
  |(ArithmeticCrossV1 g h).im| ≤ ArithmeticDiagonalV1 g

/-- Translation by zero is exactly the original repository packet. -/
theorem translatePacket_zero_v1 (g : WeilCompactSmoothGV1) :
    translatePacket g 0 = g := by
  apply Subtype.ext
  funext x
  simp [translatePacket_apply]

/-- The actual arithmetic two-point expansion is exactly the existing abstract
WeilTwoPointValueV1, after reversing the arithmetic RHS sign. -/
theorem neg_actual_two_point_eq_weil_two_point_v1
    (g h : WeilCompactSmoothGV1) (c : ℂ)
    (hdiag : (AEGIS.WeilMixedAlgebraV2.B h h).re =
      (AEGIS.WeilMixedAlgebraV2.B g g).re) :
    -(WeilExplicitRightSideV1
        (WeilAutocorrelationV1 (TwoPointPacketV1 g h c))).re =
      WeilTwoPointValueV1
        (ArithmeticDiagonalV1 g)
        (ArithmeticCrossV1 g h)
        c := by
  unfold TwoPointPacketV1
  rw [AEGIS.WeilMixedAlgebraV2.actual_expansion]
  unfold ArithmeticDiagonalV1 ArithmeticCrossV1
  unfold AEGIS.WeilThreeBlockComplexV2.diagonal
    AEGIS.WeilThreeBlockComplexV2.cross
    WeilTwoPointValueV1
  rw [AEGIS.WeilMixedAlgebraV2.B_hermitian g h]
  simp only [norm_one, one_pow, norm_zero, mul_one, mul_zero,
    zero_mul, add_zero, Complex.star_def, one_mul,
    Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, Complex.sq_norm, Complex.normSq_apply,
    map_zero]
  rw [hdiag]
  ring

/-- Component dominance gives actual arithmetic nonpositivity for every one of
the four criterion phases, provided the two translated packets have equal
diagonal value. -/
theorem component_bounds_imply_four_phase_rhs_nonpositive_v1
    (g h : WeilCompactSmoothGV1)
    (hdiag : (AEGIS.WeilMixedAlgebraV2.B h h).re =
      (AEGIS.WeilMixedAlgebraV2.B g g).re)
    (hb : ArithmeticComponentBoundsV1 g h)
    (c : ℂ) (hc : WeilFourPhaseV1 c) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (TwoPointPacketV1 g h c))).re ≤ 0 := by
  have hphase :
      0 ≤ WeilTwoPointValueV1
        (ArithmeticDiagonalV1 g)
        (ArithmeticCrossV1 g h)
        c :=
    (weil_four_phase_nonnegative_iff_components_v1
      (ArithmeticDiagonalV1 g) (ArithmeticCrossV1 g h)).2 hb c hc
  rw [← neg_actual_two_point_eq_weil_two_point_v1 g h c hdiag] at hphase
  linarith

/-- Universal actual-zeta two-point component dominance at zero translation.
The moment premise matches the exact restricted Bombieri class. -/
def ZeroShiftComponentDominanceV1 : Prop :=
  ∀ g : WeilCompactSmoothGV1,
    WeilMomentConditionsV1 g →
    ArithmeticComponentBoundsV1 g (translatePacket g 0)

/-- Zero-shift component dominance immediately yields the actual arithmetic
sign for each test packet. -/
theorem final_sign_of_zero_shift_component_dominance_v1
    (h : ZeroShiftComponentDominanceV1) :
    AEGIS.RHFinalClosureV1.FinalSignResidualV1 := by
  intro g hm
  have hb := h g hm
  rw [translatePacket_zero_v1] at hb
  have hre := hb.1
  unfold ArithmeticComponentBoundsV1 ArithmeticCrossV1 ArithmeticDiagonalV1 at hre
  simp only [Complex.neg_re, Complex.conj_re] at hre
  have habs : 0 ≤ |-(AEGIS.WeilMixedAlgebraV2.B g g).re| := abs_nonneg _
  change (AEGIS.WeilMixedAlgebraV2.B g g).re ≤ 0
  linarith

/-- Conversely, the final arithmetic sign gives the zero-shift component box.
Thus the RKHS zero-shift dominance target is not an auxiliary strengthening:
it is exactly the final sign proposition in a 2x2 component representation. -/
theorem zero_shift_component_dominance_of_final_sign_v1
    (h : AEGIS.RHFinalClosureV1.FinalSignResidualV1) :
    ZeroShiftComponentDominanceV1 := by
  intro g hm
  have hsign := h g hm
  change (AEGIS.WeilMixedAlgebraV2.B g g).re ≤ 0 at hsign
  rw [translatePacket_zero_v1]
  have hBim : (AEGIS.WeilMixedAlgebraV2.B g g).im = 0 := by
    have hh := congrArg Complex.im
      (AEGIS.WeilMixedAlgebraV2.B_hermitian g g)
    simp only [Complex.conj_im] at hh
    linarith
  unfold ArithmeticComponentBoundsV1 ArithmeticCrossV1 ArithmeticDiagonalV1
  constructor
  · simp only [Complex.neg_re, Complex.conj_re]
    rw [abs_of_nonneg (by linarith : 0 ≤ -(AEGIS.WeilMixedAlgebraV2.B g g).re)]
  · simp only [Complex.neg_im, Complex.conj_im, hBim, neg_zero, abs_zero]
    linarith

/-- Exact equivalence between the actual zero-shift RKHS component target and
the final arithmetic sign residual. -/
theorem zero_shift_component_dominance_iff_final_sign_v1 :
    ZeroShiftComponentDominanceV1 ↔
      AEGIS.RHFinalClosureV1.FinalSignResidualV1 :=
  ⟨final_sign_of_zero_shift_component_dominance_v1,
    zero_shift_component_dominance_of_final_sign_v1⟩

end AEGIS.RHTranslatedKernelDominanceV1

#print axioms AEGIS.RHTranslatedKernelDominanceV1.translatePacket_zero_v1
#print axioms AEGIS.RHTranslatedKernelDominanceV1.neg_actual_two_point_eq_weil_two_point_v1
#print axioms AEGIS.RHTranslatedKernelDominanceV1.component_bounds_imply_four_phase_rhs_nonpositive_v1
#print axioms AEGIS.RHTranslatedKernelDominanceV1.final_sign_of_zero_shift_component_dominance_v1
#print axioms AEGIS.RHTranslatedKernelDominanceV1.zero_shift_component_dominance_of_final_sign_v1
#print axioms AEGIS.RHTranslatedKernelDominanceV1.zero_shift_component_dominance_iff_final_sign_v1
