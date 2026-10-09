import RHFourBlockConcreteV3
import RestrictedWeilCriterionKernelBridgeV10
import WeilAutocorrelationExplicitFormulaV10
import WeilRHImpliesFinalSignV13
import Mathlib.Tactic

/-!
AEGIS Ω — Weil positivity on the four-translate family, V13.

`RHFourBlockConcreteV3.four_packet_coercive_v3` gives, for every compact-smooth
moment-zero packet `g` of log-support width ≤ 1/64 and every coefficient
quadruple `z ∈ ℂ⁴`, the strict arithmetic-side sign

  Re RHS(Autocorr(fourPacket g z)) ≤ −(2/125)·E(g)·energy4(‖z‖) ≤ 0.

The whole explicit formula (V10) converts this to nonnegativity of the
canonical zero quadratic on the same family.  So the RH-equivalent predicate
`UniversalZeroQuadraticNonnegativeV10` holds, unconditionally, on the
four-translate span of every narrow packet.

This is a partial verification on a 4-parameter family per seed.  It is NOT
`UniversalZeroQuadraticNonnegativeV10` (which quantifies over all `g`), and
therefore NOT RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourPacketZeroQuadraticV13

open AEGIS.RHFourBlockConcreteV3
open AEGIS.RHNarrowDiagonalUpgradeV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilMixedAlgebraV2
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHMillenniumGateV10
open AEGIS.RHFourBlockActualBridgeV2
open AEGIS.RHFineMomentPacketV3

/-- The four-translate combination stays in the moment-zero class. -/
theorem fourPacket_moments_v13 (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) (z0 z1 z2 z3 : ℂ) :
    WeilMomentConditionsV1 (fourPacket g z0 z1 z2 z3) := by
  obtain ⟨h0, h1, h2, h3⟩ := four_packet_moments_v3 g hm
  unfold fourPacket combo4
  exact addPacket_preserves_moments_v10 _ _
    (combo_preserves_moments_v10 z0 z1 z2 _ _ _ h0 h1 h2)
    (scalePacket_preserves_moments_v10 z3 _ h3)

/-- Arithmetic side is nonpositive on the four-translate family. -/
theorem fourPacket_arithmetic_nonpositive_v13 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) (hm : WeilMomentConditionsV1 g)
    (z0 z1 z2 z3 : ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket g z0 z1 z2 z3))).re ≤ 0 := by
  have hb := four_packet_coercive_v3 g a hw hm z0 z1 z2 z3
  have hS : 0 ≤ AEGIS.RHFourBlockComparisonV2.energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ := by
    unfold AEGIS.RHFourBlockComparisonV2.energy4
    positivity
  have hE := AEGIS.WeilDisjointEnergyV2.energy_nonnegative g.1
  nlinarith [mul_nonneg hE hS]

/-- Weil positivity of the canonical zero quadratic on the four-translate
family of every narrow moment-zero packet.  Unconditional. -/
theorem fourPacket_zero_quadratic_nonnegative_v13 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) (hm : WeilMomentConditionsV1 g)
    (z0 z1 z2 z3 : ℂ) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1
            (WeilAutocorrelationV1 (fourPacket g z0 z1 z2 z3)) rho).re :=
  (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10
      (fourPacket g z0 z1 z2 z3) (fourPacket_moments_v13 g hm z0 z1 z2 z3)).mp
    (fourPacket_arithmetic_nonpositive_v13 g a hw hm z0 z1 z2 z3)

/-- The canonical seed instance: a concrete nonzero family on which the
RH-equivalent quadratic is verified. -/
theorem canonical_zero_quadratic_nonnegative_v13 (z0 z1 z2 z3 : ℂ) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1
            (WeilAutocorrelationV1 (fourPacket gFine z0 z1 z2 z3)) rho).re :=
  fourPacket_zero_quadratic_nonnegative_v13 gFine 0
    AEGIS.RHFineMomentPacketV3.gFine_width_v3
    AEGIS.RHFineMomentPacketV3.gFine_moments_v3 z0 z1 z2 z3

/-- What universality would still require, stated exactly: the same
inequality for every moment-zero `g`, not only four-translate packets. -/
theorem universal_iff_rh_restated_v13 :
    UniversalZeroQuadraticNonnegativeV10 ↔ RiemannHypothesis :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_iff_universal_v13.symm

end AEGIS.RHFourPacketZeroQuadraticV13

#print axioms AEGIS.RHFourPacketZeroQuadraticV13.fourPacket_moments_v13
#print axioms AEGIS.RHFourPacketZeroQuadraticV13.fourPacket_zero_quadratic_nonnegative_v13
#print axioms AEGIS.RHFourPacketZeroQuadraticV13.canonical_zero_quadratic_nonnegative_v13
