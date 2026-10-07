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

import WeilZeroKernelHermitianV11
import WeilTwoPointPositivityV1

/-!
# Four-phase boundedness for one fixed repository packet

Only the arithmetic signs of the four translated combinations of one packet
are assumed. The repository explicit formula and Hermitian expansion convert
these signs into a uniform bound on its canonical zero translation kernel.
No universal final-sign hypothesis is used.
-/

open Complex
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFixedPacketFourPhaseV1

open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- The actual arithmetic four-phase tests for one fixed packet and all shifts. -/
def FixedPacketFourPhaseSignV1 (g : WeilCompactSmoothGV1) : Prop :=
  ∀ (d : ℝ) (c : ℂ), WeilFourPhaseV1 c →
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (WeilTwoPointTranslateV11 g d c))).re ≤ 0

/-- The Hermitian expansion has exactly the existing scalar four-phase form. -/
theorem twoPoint_zero_quadratic_re_eq_four_phase_value
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (d : ℝ) (c : ℂ) :
    (WeilAutocorrelationZeroQuadraticV11 (WeilTwoPointTranslateV11 g d c)).re =
      WeilTwoPointValueV1 (WeilAutocorrelationZeroQuadraticV11 g).re
        (WeilZeroTranslationKernelV11 g d) c := by
  rw [twoPoint_zero_quadratic_hermitian_v11 g d c hm]
  simp only [WeilTwoPointValueV1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  ring

/-- Exact arithmetic-to-zero sign conversion, for a single tested combination. -/
theorem fixed_packet_four_phase_zero_nonnegative
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : FixedPacketFourPhaseSignV1 g) (d : ℝ) (c : ℂ)
    (hc : WeilFourPhaseV1 c) :
    0 ≤ (WeilAutocorrelationZeroQuadraticV11 (WeilTwoPointTranslateV11 g d c)).re := by
  have hp := twoPointTranslate_preserves_moments_v11 g d c hm
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    (WeilTwoPointTranslateV11 g d c) hp).mp (h d c hc)

/-- Four signs at one shift give the exact component box for that shift. -/
theorem fixed_packet_four_phase_component_bounds
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : FixedPacketFourPhaseSignV1 g) (d : ℝ) :
    |(WeilZeroTranslationKernelV11 g d).re| ≤
        (WeilAutocorrelationZeroQuadraticV11 g).re ∧
      |(WeilZeroTranslationKernelV11 g d).im| ≤
        (WeilAutocorrelationZeroQuadraticV11 g).re := by
  apply weil_four_phase_nonnegative_components_v1
  intro c hc
  rw [← twoPoint_zero_quadratic_re_eq_four_phase_value g hm d c]
  exact fixed_packet_four_phase_zero_nonnegative g hm h d c hc

/-- The same explicit constant works for every real shift of this packet. -/
theorem fixed_packet_four_phase_norm_bound
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : FixedPacketFourPhaseSignV1 g) (d : ℝ) :
    ‖WeilZeroTranslationKernelV11 g d‖ ≤
      2 * (WeilAutocorrelationZeroQuadraticV11 g).re := by
  obtain ⟨hre, him⟩ := fixed_packet_four_phase_component_bounds g hm h d
  calc
    ‖WeilZeroTranslationKernelV11 g d‖ ≤
        |(WeilZeroTranslationKernelV11 g d).re| +
          |(WeilZeroTranslationKernelV11 g d).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * (WeilAutocorrelationZeroQuadraticV11 g).re := by linarith

/-- Boundedness interface for a detecting packet; its only sign input concerns
this one packet's four translated combinations. -/
theorem fixed_packet_four_phase_implies_bounded_zero_kernel
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : FixedPacketFourPhaseSignV1 g) :
    ∃ C : ℝ, ∀ d : ℝ, ‖WeilZeroTranslationKernelV11 g d‖ ≤ C :=
  ⟨2 * (WeilAutocorrelationZeroQuadraticV11 g).re,
    fixed_packet_four_phase_norm_bound g hm h⟩

end AEGIS.RHFixedPacketFourPhaseV1

#print axioms AEGIS.RHFixedPacketFourPhaseV1.twoPoint_zero_quadratic_re_eq_four_phase_value
#print axioms AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_zero_nonnegative
#print axioms AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_component_bounds
#print axioms AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_norm_bound
#print axioms AEGIS.RHFixedPacketFourPhaseV1.fixed_packet_four_phase_implies_bounded_zero_kernel
