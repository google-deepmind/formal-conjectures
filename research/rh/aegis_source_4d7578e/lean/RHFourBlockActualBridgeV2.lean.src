import RHFourBlockComparisonV2
import WeilMixedAlgebraV2
import Mathlib.Tactic

/-!
AEGIS Omega -- conditional four-packet bridge to the actual repository B.

This extends the existing three-packet algebra to four packets. All four
diagonal and all six off-diagonal analytic premises are explicit. In
particular this file does NOT prove the new 32/25 diagonal or 13/50 farthest
bound. It is not a density/globalization theorem and does not assert RH.
Source compilation and an actual axiom audit are required before claiming
Lean kernel verification. No new axiom declaration or placeholder is used.
-/

open Complex
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFourBlockActualBridgeV2
open AEGIS.RHFourBlockComparisonV2
open AEGIS.WeilMixedAlgebraV2

def fourValue (z0 z1 z2 z3 : ℂ) (D0 D1 D2 D3 : ℝ)
    (b01 b02 b03 b12 b13 b23 : ℂ) : ℝ :=
  -(‖z0‖ ^ 2 * D0 + ‖z1‖ ^ 2 * D1 + ‖z2‖ ^ 2 * D2 + ‖z3‖ ^ 2 * D3) +
  2 * ((z0 * star z1 * b01).re + (z0 * star z2 * b02).re +
       (z0 * star z3 * b03).re + (z1 * star z2 * b12).re +
       (z1 * star z3 * b13).re + (z2 * star z3 * b23).re)

theorem pair_re_le_v2 (z w b : ℂ) (c E : ℝ) (hb : ‖b‖ ≤ c * E) :
    (z * star w * b).re ≤ c * E * ‖z‖ * ‖w‖ := by
  calc
    (z * star w * b).re ≤ ‖z * star w * b‖ := Complex.re_le_norm _
    _ = (‖z‖ * ‖w‖) * ‖b‖ := by simp only [norm_mul, norm_star]
    _ ≤ (‖z‖ * ‖w‖) * (c * E) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = c * E * ‖z‖ * ‖w‖ := by ring

/-- All-coefficient complex bound. No pair, phase, or zero-energy case is omitted. -/
theorem four_value_bound_v2
    (z0 z1 z2 z3 : ℂ) (D0 D1 D2 D3 E : ℝ)
    (b01 b02 b03 b12 b13 b23 : ℂ) (hE : 0 ≤ E)
    (h0 : (32 / 25 : ℝ) * E ≤ D0) (h1 : (32 / 25 : ℝ) * E ≤ D1)
    (h2 : (32 / 25 : ℝ) * E ≤ D2) (h3 : (32 / 25 : ℝ) * E ≤ D3)
    (h01 : ‖b01‖ ≤ (51 / 100 : ℝ) * E)
    (h02 : ‖b02‖ ≤ (9 / 25 : ℝ) * E)
    (h03 : ‖b03‖ ≤ (13 / 50 : ℝ) * E)
    (h12 : ‖b12‖ ≤ (51 / 100 : ℝ) * E)
    (h13 : ‖b13‖ ≤ (9 / 25 : ℝ) * E)
    (h23 : ‖b23‖ ≤ (51 / 100 : ℝ) * E) :
    fourValue z0 z1 z2 z3 D0 D1 D2 D3 b01 b02 b03 b12 b13 b23 ≤
      -(2 / 125 : ℝ) * E * energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ := by
  have hd0 := mul_le_mul_of_nonneg_left h0 (sq_nonneg ‖z0‖)
  have hd1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z1‖)
  have hd2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖z2‖)
  have hd3 := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖z3‖)
  have hp01 := pair_re_le_v2 z0 z1 b01 (51 / 100) E h01
  have hp02 := pair_re_le_v2 z0 z2 b02 (9 / 25) E h02
  have hp03 := pair_re_le_v2 z0 z3 b03 (13 / 50) E h03
  have hp12 := pair_re_le_v2 z1 z2 b12 (51 / 100) E h12
  have hp13 := pair_re_le_v2 z1 z3 b13 (9 / 25) E h13
  have hp23 := pair_re_le_v2 z2 z3 b23 (51 / 100) E h23
  have hc := mul_le_mul_of_nonneg_left
    (cross_le_158_over_125_v2 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖) hE
  unfold fourValue energy4 cross4 at *
  nlinarith only [hd0, hd1, hd2, hd3, hp01, hp02, hp03, hp12, hp13, hp23, hc]

def combo4 (z0 z1 z2 z3 : ℂ)
    (g0 g1 g2 g3 : WeilCompactSmoothGV1) : WeilCompactSmoothGV1 :=
  addPacket (combo z0 z1 z2 g0 g1 g2) (scalePacket z3 g3)

private theorem self_im_zero (g : WeilCompactSmoothGV1) : (B g g).im = 0 := by
  have h := congrArg Complex.im (B_hermitian g g)
  simp only [Complex.conj_im] at h
  linarith

/-- Exact expansion for the same B used by the inherited V2/V3.1 spine,
not a supplied matrix with unproved semantic correspondence. -/
theorem actual_four_block_expansion_v2 (z0 z1 z2 z3 : ℂ)
    (g0 g1 g2 g3 : WeilCompactSmoothGV1) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo4 z0 z1 z2 z3 g0 g1 g2 g3))).re =
    fourValue z0 z1 z2 z3
      (-(B g0 g0).re) (-(B g1 g1).re) (-(B g2 g2).re) (-(B g3 g3).re)
      (B g0 g1) (B g0 g2) (B g0 g3) (B g1 g2) (B g1 g3) (B g2 g3) := by
  change (B (combo4 z0 z1 z2 z3 g0 g1 g2 g3)
    (combo4 z0 z1 z2 z3 g0 g1 g2 g3)).re = _
  unfold combo4 combo
  simp only [B_add_left, B_add_right, B_scale_left, B_scale_right]
  rw [B_hermitian g0 g1, B_hermitian g0 g2, B_hermitian g0 g3,
      B_hermitian g1 g2, B_hermitian g1 g3, B_hermitian g2 g3]
  unfold fourValue
  simp only [Complex.star_def, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply, self_im_zero]
  ring

/-- Conditional analytic-to-algebra bridge. The stronger diagonal and the
farthest-pair estimate remain hypotheses, not verified facts about packets. -/
theorem actual_four_block_bound_v2 (z0 z1 z2 z3 : ℂ)
    (g0 g1 g2 g3 : WeilCompactSmoothGV1) (E : ℝ) (hE : 0 ≤ E)
    (h0 : (32 / 25 : ℝ) * E ≤ -(B g0 g0).re)
    (h1 : (32 / 25 : ℝ) * E ≤ -(B g1 g1).re)
    (h2 : (32 / 25 : ℝ) * E ≤ -(B g2 g2).re)
    (h3 : (32 / 25 : ℝ) * E ≤ -(B g3 g3).re)
    (h01 : ‖B g0 g1‖ ≤ (51 / 100 : ℝ) * E)
    (h02 : ‖B g0 g2‖ ≤ (9 / 25 : ℝ) * E)
    (h03 : ‖B g0 g3‖ ≤ (13 / 50 : ℝ) * E)
    (h12 : ‖B g1 g2‖ ≤ (51 / 100 : ℝ) * E)
    (h13 : ‖B g1 g3‖ ≤ (9 / 25 : ℝ) * E)
    (h23 : ‖B g2 g3‖ ≤ (51 / 100 : ℝ) * E) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo4 z0 z1 z2 z3 g0 g1 g2 g3))).re ≤
      -(2 / 125 : ℝ) * E * energy4 ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖ := by
  rw [actual_four_block_expansion_v2]
  exact four_value_bound_v2 z0 z1 z2 z3
    (-(B g0 g0).re) (-(B g1 g1).re) (-(B g2 g2).re) (-(B g3 g3).re) E
    (B g0 g1) (B g0 g2) (B g0 g3) (B g1 g2) (B g1 g3) (B g2 g3)
    hE h0 h1 h2 h3 h01 h02 h03 h12 h13 h23

end AEGIS.RHFourBlockActualBridgeV2

#print axioms AEGIS.RHFourBlockActualBridgeV2.pair_re_le_v2
#print axioms AEGIS.RHFourBlockActualBridgeV2.four_value_bound_v2
#print axioms AEGIS.RHFourBlockActualBridgeV2.actual_four_block_expansion_v2
#print axioms AEGIS.RHFourBlockActualBridgeV2.actual_four_block_bound_v2
