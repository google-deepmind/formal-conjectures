import RHThreeCellGainV13
import RHThresholdClassV13
import WeilThreeBlockAnalyticConstantsV21
import Mathlib.Tactic

/-!
AEGIS Ω — Weil positivity on the half-width-7/32 class, V13.

`cellGain (5/32) (7/32) ≤ −1/200` (closed-form value ≈ −0.0182), hence every moment-zero
packet whose logarithmic support has half-width at most `7/32` (support length `≤ 7/16`)
has `Re RHS ≤ −E/200` and a nonnegative canonical zero quadratic.  This extends the
`21/100` class of `RHBonusClassV13`.

Numerics: Taylor enclosures; the `λ`-coefficient `2 sinh r + sinh(r/2) − 6 sinh(t/2) −
sinh(s/2) ≤ 85/10000`; the four `cothTail` terms carry coefficients `−3/16, −25/16, 1/4,
1/2`, so `16·(sum) = log y − 73 log 2` with
`y = 2⁷³·X_r⁴·X_{2r}⁸ / (X_s³·X_t²⁵)`, `X_w = (1 + e^{−w})/(1 − e^{−w})`, and
`log y ≤ y − 1 ≤ 12/100`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHThreeCellClassV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHThreeCellGainV13

theorem lam_upper_5_32 : lamR (5 / 32) ≤ 3436 / 1000 := by
  obtain ⟨ht, -⟩ := exp_pos_enc (5 / 32) (by norm_num) (by norm_num)
  obtain ⟨htn, htn'⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at ht htn htn'
  have hsh : 1568848 / 10000000 ≤ Real.sinh (5 / 32) := by rw [Real.sinh_eq]; linarith
  have hq : 18553451 / 10000000 ≤ 1 + Real.exp (-(5 / 32)) := by linarith
  unfold lamR
  have hpos : 0 < Real.sinh (5 / 32) * (1 + Real.exp (-(5 / 32))) := by
    have := Real.sinh_pos_iff.mpr (by norm_num : (0 : ℝ) < 5 / 32); positivity
  rw [div_le_iff₀ hpos]
  have := mul_le_mul hsh hq (by norm_num) (by linarith)
  nlinarith

theorem lam_coeff_upper :
    -Real.sinh (7 / 96) - 6 * Real.sinh (5 / 64) + Real.sinh (7 / 64)
      + 2 * Real.sinh (7 / 32) ≤ 85 / 10000 := by
  obtain ⟨h1, -⟩ := exp_pos_enc (7 / 96) (by norm_num) (by norm_num)
  obtain ⟨-, h2⟩ := exp_neg_enc (7 / 96) (by norm_num) (by norm_num)
  obtain ⟨h3, -⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, h4⟩ := exp_neg_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, h5⟩ := exp_pos_enc (7 / 64) (by norm_num) (by norm_num)
  obtain ⟨h6, -⟩ := exp_neg_enc (7 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, h7⟩ := exp_pos_enc (7 / 32) (by norm_num) (by norm_num)
  obtain ⟨h8, -⟩ := exp_neg_enc (7 / 32) (by norm_num) (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8
  rw [Real.sinh_eq, Real.sinh_eq, Real.sinh_eq, Real.sinh_eq]
  linarith

/-- The four `cothTail` terms. -/
theorem cothTail_combo_cell :
    -(3 / 16) * cothTail (7 / 48) - (25 / 16) * cothTail (5 / 32) + cothTail (7 / 32) / 4
      + cothTail (7 / 16) / 2 ≤ (12 / 100 - 73 * Real.log 2) / 16 := by
  obtain ⟨hbl, hbu⟩ := exp_neg_enc (7 / 32) (by norm_num) (by norm_num)
  obtain ⟨hcl, hcu⟩ := exp_neg_enc (7 / 48) (by norm_num) (by norm_num)
  obtain ⟨hal, hau⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at hbl hbu hcl hcu hal hau
  set a := Real.exp (-(5 / 32 : ℝ)) with ha
  set b := Real.exp (-(7 / 32 : ℝ)) with hb
  set c := Real.exp (-(7 / 48 : ℝ)) with hc
  have hb2 : Real.exp (-(7 / 16 : ℝ)) = b ^ 2 := by
    rw [hb, sq, ← Real.exp_add]; ring_nf
  unfold cothTail
  rw [hb2]
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hc1 : 0 < 1 - c := by linarith
  have hb21 : 0 < 1 - b ^ 2 := by nlinarith
  have ha2 : 0 < 1 + a := by linarith
  have hbp : 0 < 1 + b := by linarith
  have hc2 : 0 < 1 + c := by linarith
  have hbq : 0 < 1 + b ^ 2 := by positivity
  rw [Real.log_div ha2.ne' ha1.ne', Real.log_div hbp.ne' hb1.ne', Real.log_div hc2.ne' hc1.ne',
    Real.log_div hbq.ne' hb21.ne']
  set N := (1 + b) ^ 4 * (1 + b ^ 2) ^ 8 * (1 - c) ^ 3 * (1 - a) ^ 25 with hNdef
  set D := (1 - b) ^ 4 * (1 - b ^ 2) ^ 8 * (1 + c) ^ 3 * (1 + a) ^ 25 with hDdef
  have hN0 : 0 < N := by positivity
  have hD0 : 0 < D := by positivity
  have hlogN : Real.log N = 4 * Real.log (1 + b) + 8 * Real.log (1 + b ^ 2)
      + 3 * Real.log (1 - c) + 25 * Real.log (1 - a) := by
    rw [hNdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have hlogD : Real.log D = 4 * Real.log (1 - b) + 8 * Real.log (1 - b ^ 2)
      + 3 * Real.log (1 + c) + 25 * Real.log (1 + a) := by
    rw [hDdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  set y := (2 : ℝ) ^ 73 * N / D with hy
  have hy0 : 0 < y := by positivity
  have hlogy : Real.log y = 73 * Real.log 2 + Real.log N - Real.log D := by
    rw [hy, Real.log_div (by positivity) hD0.ne', Real.log_mul (by positivity) hN0.ne',
      Real.log_pow]
    push_cast; ring
  have hb' : b ≤ 8035317 / 10000000 := by linarith
  have hbsq : b ^ 2 ≤ (8035317 / 10000000 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le hb' 2
  have hN : N ≤
      (1 + 8035317 / 10000000) ^ 4 * (1 + (8035317 / 10000000 : ℝ) ^ 2) ^ 8 *
        (1 - 8643016 / 10000000) ^ 3 * (1 - 8553451 / 10000000) ^ 25 := by
    have e1 : (1 + b) ^ 4 ≤ (1 + 8035317 / 10000000 : ℝ) ^ 4 :=
      by gcongr
    have e2 : (1 + b ^ 2) ^ 8 ≤ (1 + (8035317 / 10000000 : ℝ) ^ 2) ^ 8 :=
      by gcongr
    have e3 : (1 - c) ^ 3 ≤ (1 - 8643016 / 10000000 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hc1.le (by linarith) 3
    have e4 : (1 - a) ^ 25 ≤ (1 - 8553451 / 10000000 : ℝ) ^ 25 :=
      pow_le_pow_left₀ ha1.le (by linarith) 25
    have p12 := mul_le_mul e1 e2 (by positivity) (by positivity)
    have p123 := mul_le_mul p12 e3 (by positivity) (by positivity)
    exact mul_le_mul p123 e4 (by positivity) (by positivity)
  have hD : (1 - 8035317 / 10000000) ^ 4 * (1 - (8035317 / 10000000 : ℝ) ^ 2) ^ 8 *
        (1 + 8643016 / 10000000) ^ 3 * (1 + 8553451 / 10000000) ^ 25 ≤ D := by
    have hb0 : 0 ≤ b := (Real.exp_pos _).le
    show _ ≤ (1 - b) ^ 4 * (1 - b ^ 2) ^ 8 * (1 + c) ^ 3 * (1 + a) ^ 25
    gcongr <;> linarith
  have hnum : 2 ^ 73 * ((1 + 8035317 / 10000000) ^ 4 * (1 + (8035317 / 10000000 : ℝ) ^ 2) ^ 8 *
        (1 - 8643016 / 10000000) ^ 3 * (1 - 8553451 / 10000000) ^ 25) ≤
      (112 / 100) * ((1 - 8035317 / 10000000) ^ 4 * (1 - (8035317 / 10000000 : ℝ) ^ 2) ^ 8 *
        (1 + 8643016 / 10000000) ^ 3 * (1 + 8553451 / 10000000) ^ 25) := by norm_num
  have hyle : y ≤ 112 / 100 := by
    rw [hy, div_le_iff₀ hD0]
    have hN' := mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 2 ^ 73)
    have hD' := mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 112 / 100)
    exact le_trans hN' (le_trans hnum hD')
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [hlogy, hlogN, hlogD] at hlog
  linarith

/-- `cellGain (5/32) (7/32) ≤ −1/200`. -/
theorem cellGain_5_32_7_32 : cellGain (5 / 32) (7 / 32) ≤ -(1 / 200) := by
  have hL := lam_upper_5_32
  have hL0 : 0 < lamR (5 / 32) := lamR_pos _ (by norm_num)
  have hD := lam_coeff_upper
  have hcombo := cothTail_combo_cell
  obtain ⟨-, hs⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  norm_num at hs
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  have e1 : 2 * (7 / 32 : ℝ) / 3 = 7 / 48 := by norm_num
  have e2 : (7 / 48 : ℝ) / 2 = 7 / 96 := by norm_num
  have e3 : (5 / 32 : ℝ) / 2 = 5 / 64 := by norm_num
  have e4 : (7 / 32 : ℝ) / 2 = 7 / 64 := by norm_num
  have e5 : 2 * (7 / 32 : ℝ) = 7 / 16 := by norm_num
  set L := lamR (5 / 32)
  set D := -Real.sinh (7 / 96) - 6 * Real.sinh (5 / 64) + Real.sinh (7 / 64)
    + 2 * Real.sinh (7 / 32) with hDdef
  have hLD : L * D ≤ 3436 / 1000 * (85 / 10000) := by
    have h1 : L * D ≤ L * (85 / 10000) := mul_le_mul_of_nonneg_left hD hL0.le
    nlinarith
  have hA : cellArch (5 / 32) (7 / 32) = (7 / 96) * Real.exp (5 / 64) + L * D
      - (3 / 4) * (7 / 32 - 5 / 32) / 2 - 7 / 32 / 4
      + (-(3 / 16) * cothTail (7 / 48) - (25 / 16) * cothTail (5 / 32)
        + cothTail (7 / 32) / 4 + cothTail (7 / 16) / 2) := by
    unfold cellArch
    rw [e1, e2, e3, e4, e5, hDdef]
    ring
  unfold cellGain
  rw [hA]
  linarith

theorem cell_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (7 / 32) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 200) * energy g.1 := by
  have hlog : 2 * (7 / 32 : ℝ) < Real.log 2 := by linarith [log_two_lower]
  obtain ⟨-, hs⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  norm_num at hs
  have hexp : Real.exp ((5 / 32 : ℝ) / 2) ≤ 13 / 12 := by
    rw [show (5 / 32 : ℝ) / 2 = 5 / 64 by norm_num]; linarith
  have hd := cell_diagonal g (5 / 32) (7 / 32) a (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hexp hlog hw hm
  have hg := mul_le_mul_of_nonneg_right cellGain_5_32_7_32 (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`7/32` class.** -/
theorem universal_on_cell_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (7 / 32) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := cell_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHThreeCellClassV13

#print axioms AEGIS.RHThreeCellClassV13.cellGain_5_32_7_32
#print axioms AEGIS.RHThreeCellClassV13.cell_coercive
#print axioms AEGIS.RHThreeCellClassV13.universal_on_cell_class
