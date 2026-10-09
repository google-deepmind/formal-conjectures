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

import RHFixedPacketFrontierV1
import FormalConjectures.Millennium.RHSnowflakeLog23
import RHZeroKernelLaplaceAnalyticV12

/-!
# Dense logarithmic shifts suffice for the fixed detecting packet

Continuity of the actual canonical zero translation kernel makes each of the
four scalar Hermitian tests continuous in its shift. The proved density of
Z log 2 + Z log 3 therefore extends their arithmetic signs to all real shifts.
This uses density of shift locations only. No density of a translated-function
span, approximation theorem, or universal sign assumption is introduced.
-/

open Complex

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFixedPacketDenseShiftV1

open RHSnowflakeLog23
open AEGIS.RHFixedPacketFourPhaseV1
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.WeilZeroTranslationV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHZeroKernelLaplaceAnalyticV12

/-- Four actual arithmetic signs for one packet on the dense logarithmic group. -/
def DensePacketFourPhaseSignV1 (g : WeilCompactSmoothGV1) : Prop :=
  ∀ d : ℝ, d ∈ SnowflakeShiftGroup →
    ∀ c : ℂ, WeilFourPhaseV1 c →
      (WeilExplicitRightSideV1
        (WeilAutocorrelationV1 (WeilTwoPointTranslateV11 g d c))).re ≤ 0

/-- The single remaining sign statement for the unconditionally chosen detector. -/
def DenseFixedPacketSign : Prop := DensePacketFourPhaseSignV1 detectingPacket

/-- The scalar four-phase test is continuous in the actual real shift. -/
theorem translated_four_phase_value_continuous (g : WeilCompactSmoothGV1) (c : ℂ) :
    Continuous (fun d : ℝ =>
      WeilTwoPointValueV1 (WeilAutocorrelationZeroQuadraticV11 g).re
        (WeilZeroTranslationKernelV11 g d) c) := by
  have hK := zero_translation_kernel_continuous_v12 g
  have hcK : Continuous (fun d : ℝ => c * WeilZeroTranslationKernelV11 g d) :=
    continuous_const.mul hK
  have hre : Continuous (fun d : ℝ => (c * WeilZeroTranslationKernelV11 g d).re) :=
    Complex.continuous_re.comp hcK
  unfold WeilTwoPointValueV1
  exact continuous_const.add (continuous_const.mul hre)

/-- Dense shift signs extend to all shifts for this same packet. -/
theorem dense_packet_four_phase_implies_all_shifts
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (h : DensePacketFourPhaseSignV1 g) : FixedPacketFourPhaseSignV1 g := by
  intro d c hc
  have hnonneg : ∀ x : ℝ,
      0 ≤ WeilTwoPointValueV1 (WeilAutocorrelationZeroQuadraticV11 g).re
        (WeilZeroTranslationKernelV11 g x) c := by
    apply snowflake_nonnegative_of_continuous
      (fun x : ℝ => WeilTwoPointValueV1 (WeilAutocorrelationZeroQuadraticV11 g).re
        (WeilZeroTranslationKernelV11 g x) c)
      (translated_four_phase_value_continuous g c)
    intro x hx
    have hp := twoPointTranslate_preserves_moments_v11 g x c hm
    have hQ : 0 ≤
        (WeilAutocorrelationZeroQuadraticV11 (WeilTwoPointTranslateV11 g x c)).re :=
      (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
        (WeilTwoPointTranslateV11 g x c) hp).mp (h x hx c hc)
    rw [twoPoint_zero_quadratic_re_eq_four_phase_value g hm x c] at hQ
    exact hQ
  apply (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
    (WeilTwoPointTranslateV11 g d c)
    (twoPointTranslate_preserves_moments_v11 g d c hm)).mpr
  change 0 ≤ (WeilAutocorrelationZeroQuadraticV11 (WeilTwoPointTranslateV11 g d c)).re
  rw [twoPoint_zero_quadratic_re_eq_four_phase_value g hm d c]
  exact hnonneg d

/-- The dense-group and all-real-shift statements for the detector are equivalent. -/
theorem dense_fixed_packet_sign_iff_fixed_sign :
    DenseFixedPacketSign ↔ FixedDetectingPacketSign := by
  constructor
  · intro h
    exact dense_packet_four_phase_implies_all_shifts detectingPacket detectingPacket_moments h
  · intro h d _hd c hc
    exact h d c hc

/-- Producing the dense-group signs gives the original universal AEGIS residual. -/
theorem universal_of_dense_fixed_packet_sign (h : DenseFixedPacketSign) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 :=
  universal_of_fixed_detecting_packet_sign (dense_fixed_packet_sign_iff_fixed_sign.mp h)

/-- The dense fixed-packet sign is exactly equivalent to the original residual. -/
theorem dense_fixed_packet_sign_iff_universal :
    DenseFixedPacketSign ↔
      AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 :=
  dense_fixed_packet_sign_iff_fixed_sign.trans fixed_detecting_packet_sign_iff_universal

/-- Producing the dense-group signs proves the actual Mathlib Riemann hypothesis. -/
theorem riemannHypothesis_of_dense_fixed_packet_sign (h : DenseFixedPacketSign) :
    RiemannHypothesis :=
  riemannHypothesis_of_fixed_detecting_packet_sign (dense_fixed_packet_sign_iff_fixed_sign.mp h)

end AEGIS.RHFixedPacketDenseShiftV1

#print axioms AEGIS.RHFixedPacketDenseShiftV1.translated_four_phase_value_continuous
#print axioms AEGIS.RHFixedPacketDenseShiftV1.dense_packet_four_phase_implies_all_shifts
#print axioms AEGIS.RHFixedPacketDenseShiftV1.dense_fixed_packet_sign_iff_fixed_sign
#print axioms AEGIS.RHFixedPacketDenseShiftV1.universal_of_dense_fixed_packet_sign
#print axioms AEGIS.RHFixedPacketDenseShiftV1.dense_fixed_packet_sign_iff_universal
#print axioms AEGIS.RHFixedPacketDenseShiftV1.riemannHypothesis_of_dense_fixed_packet_sign
