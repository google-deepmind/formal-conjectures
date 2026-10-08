import RHFourBlockPrimeEightV3
import RHFineMomentPacketV3
import RHFourBlockActualBridgeV2
import Mathlib.Tactic

/-!
AEGIS Omega -- concrete four-packet assembly, candidate V3.
This source replaces the V2 four-diagonal/six-cross analytic hypotheses by
repository moment conditions and genuine total log-support width <= 1/64.
A nonzero canonical seed witnesses this narrower class. All complex phases,
all six pairs and zero energy are retained. This is a finite-family statement,
not density, globalization, universal Weil sign or RH. Compilation NOT_RUN
until an actual pinned Lean process and transitive axiom audit establish it.
-/

open Set MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockConcreteV3
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilSeparatedArchBridgeV31
open AEGIS.RHNarrowDiagonalUpgradeV2
open AEGIS.RHFourBlockPrimeEightV3
open AEGIS.RHFineMomentPacketV3
open AEGIS.RHFourBlockActualBridgeV2
open AEGIS.RHFourBlockComparisonV2

/-- Support width is transported, not shrunk by translation. -/
theorem translate_fine_width_v3 (g : WeilCompactSmoothGV1) (a d : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    WidthOneSixtyFourAt (translatePacket g d) (a + d) := by
  have hs := translate_logSupportIn g d (a - 1 / 128) (a + 1 / 128) hw
  change LogSupportIn (translatePacket g d) (a + d - 1 / 128) (a + d + 1 / 128)
  convert hs using 1 <;> ring

theorem translated_diagonal_v3 (g : WeilCompactSmoothGV1) (a d : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    (32 / 25 : ℝ) * energy g.1 ≤
      -(B (translatePacket g d) (translatePacket g d)).re := by
  have hd := narrow_diagonal_32_over_25_v2 (translatePacket g d) (a + d)
    (translate_fine_width_v3 g a d hw)
  rw [translate_energy] at hd
  exact hd

theorem four_diagonals_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) :
    (32 / 25 : ℝ) * energy g.1 ≤ -(B (translatePacket g 0) (translatePacket g 0)).re ∧
    (32 / 25 : ℝ) * energy g.1 ≤
      -(B (translatePacket g (Real.log 2)) (translatePacket g (Real.log 2))).re ∧
    (32 / 25 : ℝ) * energy g.1 ≤
      -(B (translatePacket g (2 * Real.log 2)) (translatePacket g (2 * Real.log 2))).re ∧
    (32 / 25 : ℝ) * energy g.1 ≤
      -(B (translatePacket g (3 * Real.log 2)) (translatePacket g (3 * Real.log 2))).re :=
  ⟨translated_diagonal_v3 g a 0 hw,
   translated_diagonal_v3 g a (Real.log 2) hw,
   translated_diagonal_v3 g a (2 * Real.log 2) hw,
   translated_diagonal_v3 g a (3 * Real.log 2) hw⟩

theorem four_common_energies_v3 (g : WeilCompactSmoothGV1) :
    energy (translatePacket g 0).1 = energy g.1 ∧
    energy (translatePacket g (Real.log 2)).1 = energy g.1 ∧
    energy (translatePacket g (2 * Real.log 2)).1 = energy g.1 ∧
    energy (translatePacket g (3 * Real.log 2)).1 = energy g.1 :=
  ⟨translate_energy g 0, translate_energy g (Real.log 2),
   translate_energy g (2 * Real.log 2), translate_energy g (3 * Real.log 2)⟩

theorem four_packet_moments_v3 (g : WeilCompactSmoothGV1)
    (hm : WeilMomentConditionsV1 g) :
    WeilMomentConditionsV1 (translatePacket g 0) ∧
    WeilMomentConditionsV1 (translatePacket g (Real.log 2)) ∧
    WeilMomentConditionsV1 (translatePacket g (2 * Real.log 2)) ∧
    WeilMomentConditionsV1 (translatePacket g (3 * Real.log 2)) :=
  ⟨translate_preserves_moments g 0 hm, translate_preserves_moments g (Real.log 2) hm,
   translate_preserves_moments g (2 * Real.log 2) hm,
   translate_preserves_moments g (3 * Real.log 2) hm⟩

theorem adjacent_B_of_gap_v3 (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g)
    (hgap : d2 - d1 = Real.log 2) :
    ‖B (translatePacket g d1) (translatePacket g d2)‖ ≤
      (51 / 100 : ℝ) * energy g.1 := by
  rw [B_translate_eq_of_gap_v3 g d1 d2 (-Real.log 2) 0 (by linarith)]
  exact (three_cross_bounds_of_moments g a hw hm).1

theorem next_B_of_gap_v3 (g : WeilCompactSmoothGV1) (a d1 d2 : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g)
    (hgap : d2 - d1 = 2 * Real.log 2) :
    ‖B (translatePacket g d1) (translatePacket g d2)‖ ≤
      (9 / 25 : ℝ) * energy g.1 := by
  rw [B_translate_eq_of_gap_v3 g d1 d2 (-Real.log 2) (Real.log 2) (by linarith)]
  exact (three_cross_bounds_of_moments g a hw hm).2.1

/-- Complete graph: 01,02,03,12,13,23. In particular 03 is derived from n=8. -/
theorem six_cross_bounds_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneThirtyTwoAt g a) (hm : WeilMomentConditionsV1 g) :
    ‖B (translatePacket g 0) (translatePacket g (Real.log 2))‖ ≤
      (51 / 100 : ℝ) * energy g.1 ∧
    ‖B (translatePacket g 0) (translatePacket g (2 * Real.log 2))‖ ≤
      (9 / 25 : ℝ) * energy g.1 ∧
    ‖B (translatePacket g 0) (translatePacket g (3 * Real.log 2))‖ ≤
      (13 / 50 : ℝ) * energy g.1 ∧
    ‖B (translatePacket g (Real.log 2)) (translatePacket g (2 * Real.log 2))‖ ≤
      (51 / 100 : ℝ) * energy g.1 ∧
    ‖B (translatePacket g (Real.log 2)) (translatePacket g (3 * Real.log 2))‖ ≤
      (9 / 25 : ℝ) * energy g.1 ∧
    ‖B (translatePacket g (2 * Real.log 2)) (translatePacket g (3 * Real.log 2))‖ ≤
      (51 / 100 : ℝ) * energy g.1 :=
  ⟨adjacent_B_of_gap_v3 g a 0 (Real.log 2) hw hm (by ring),
   next_B_of_gap_v3 g a 0 (2 * Real.log 2) hw hm (by ring),
   farthest_B_norm_bound_v3 g a hw hm,
   adjacent_B_of_gap_v3 g a (Real.log 2) (2 * Real.log 2) hw hm (by ring),
   next_B_of_gap_v3 g a (Real.log 2) (3 * Real.log 2) hw hm (by ring),
   adjacent_B_of_gap_v3 g a (2 * Real.log 2) (3 * Real.log 2) hw hm (by ring)⟩

def fourPacket (g : WeilCompactSmoothGV1) (z0 z1 z2 z3 : ℂ) : WeilCompactSmoothGV1 :=
  combo4 z0 z1 z2 z3 (translatePacket g 0) (translatePacket g (Real.log 2))
    (translatePacket g (2 * Real.log 2)) (translatePacket g (3 * Real.log 2))

/-- No supplied diagonal, cross-bound, matrix-PSD or sign hypothesis remains
in this finite-family statement. The analytic class conditions stay explicit. -/
theorem four_packet_coercive_v3 (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : WidthOneSixtyFourAt g a) (hm : WeilMomentConditionsV1 g)
    (z0 z1 z2 z3 : ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket g z0 z1 z2 z3))).re ≤
      -(2 / 125 : ℝ) * energy g.1 * energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ := by
  obtain ⟨h0, h1, h2, h3⟩ := four_diagonals_v3 g a hw
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
    six_cross_bounds_v3 g a (narrow_implies_retained_v2 g a hw) hm
  exact actual_four_block_bound_v2 z0 z1 z2 z3
    (translatePacket g 0) (translatePacket g (Real.log 2))
    (translatePacket g (2 * Real.log 2)) (translatePacket g (3 * Real.log 2))
    (energy g.1) (energy_nonnegative g.1)
    h0 h1 h2 h3 h01 h02 h03 h12 h13 h23

theorem canonical_fine_packet_exists_v3 :
    ∃ g : WeilCompactSmoothGV1,
      WidthOneSixtyFourAt g 0 ∧ WeilMomentConditionsV1 g ∧ g.1 ≠ 0 :=
  ⟨gFine, gFine_width_v3, gFine_moments_v3, gFine_ne_zero_v3⟩

theorem canonical_four_packet_coercive_v3 (z0 z1 z2 z3 : ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket gFine z0 z1 z2 z3))).re ≤
      -(2 / 125 : ℝ) * energy gFine.1 * energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ :=
  four_packet_coercive_v3 gFine 0 gFine_width_v3 gFine_moments_v3 z0 z1 z2 z3

theorem canonical_four_packet_sign_v3 (z0 z1 z2 z3 : ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket gFine z0 z1 z2 z3))).re ≤ 0 := by
  have hb := canonical_four_packet_coercive_v3 z0 z1 z2 z3
  have hS : 0 ≤ energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ := by
    unfold energy4
    positivity
  have hE := energy_nonnegative gFine.1
  have hp := mul_nonneg hE hS
  nlinarith

end AEGIS.RHFourBlockConcreteV3

#print axioms AEGIS.RHFourBlockConcreteV3.translate_fine_width_v3
#print axioms AEGIS.RHFourBlockConcreteV3.translated_diagonal_v3
#print axioms AEGIS.RHFourBlockConcreteV3.four_diagonals_v3
#print axioms AEGIS.RHFourBlockConcreteV3.four_common_energies_v3
#print axioms AEGIS.RHFourBlockConcreteV3.four_packet_moments_v3
#print axioms AEGIS.RHFourBlockConcreteV3.adjacent_B_of_gap_v3
#print axioms AEGIS.RHFourBlockConcreteV3.next_B_of_gap_v3
#print axioms AEGIS.RHFourBlockConcreteV3.six_cross_bounds_v3
#print axioms AEGIS.RHFourBlockConcreteV3.four_packet_coercive_v3
#print axioms AEGIS.RHFourBlockConcreteV3.canonical_fine_packet_exists_v3
#print axioms AEGIS.RHFourBlockConcreteV3.canonical_four_packet_coercive_v3
#print axioms AEGIS.RHFourBlockConcreteV3.canonical_four_packet_sign_v3
