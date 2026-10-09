import RHBonusGainV13
import RHThresholdClassV13
import WeilThreeBlockAnalyticConstantsV21
import Mathlib.Tactic

/-!
AEGIS Ω — Weil positivity on the half-width-21/100 class, V13.

`bonusGain (5/32) (21/100) ≤ −1/50` (true value ≈ −0.0463), hence every moment-zero
packet whose logarithmic support has half-width at most `21/100` (support length
`≤ 21/50`) has `Re RHS ≤ −E/50` and a nonnegative canonical zero quadratic.  This
extends the `1/5` class of `RHThresholdClassV13`.

Numerics as there: fourth-order Taylor enclosures, and the three `cothTail` logarithms
combined into `log y − 9 log 2` with `log y ≤ y − 1 ≤ −12/100`.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBonusClassV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHThresholdGainV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHBonusGainV13

/-- The λ-term at threshold `5/32`, half-width `21/100`, is at most `3436/1000 · 79/10000`. -/
theorem lam_term_5_32_21 :
    lamR (5 / 32) * (2 * Real.sinh (21 / 100) + 2 * Real.sinh ((21 / 100) / 2)
      - 8 * Real.sinh ((5 / 32) / 2)) ≤ 3436 / 1000 * (79 / 10000) := by
  obtain ⟨-, hr⟩ := exp_pos_enc (21 / 100) (by norm_num) (by norm_num)
  obtain ⟨hrn, -⟩ := exp_neg_enc (21 / 100) (by norm_num) (by norm_num)
  obtain ⟨-, hh⟩ := exp_pos_enc (21 / 200) (by norm_num) (by norm_num)
  obtain ⟨hhn, -⟩ := exp_neg_enc (21 / 200) (by norm_num) (by norm_num)
  obtain ⟨hs, -⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, hsn⟩ := exp_neg_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨ht, -⟩ := exp_pos_enc (5 / 32) (by norm_num) (by norm_num)
  obtain ⟨htn, htn'⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at hr hrn hh hhn hs hsn ht htn htn'
  have e1 : ((21 : ℝ) / 100) / 2 = 21 / 200 := by norm_num
  have e2 : ((5 : ℝ) / 32) / 2 = 5 / 64 := by norm_num
  rw [e1, e2]
  set D := 2 * Real.sinh (21 / 100) + 2 * Real.sinh (21 / 200) - 8 * Real.sinh (5 / 64) with hD
  have hDup : D ≤ 79 / 10000 := by
    rw [hD, Real.sinh_eq, Real.sinh_eq, Real.sinh_eq]
    linarith
  have hsh : 1568848 / 10000000 ≤ Real.sinh (5 / 32) := by
    rw [Real.sinh_eq]; linarith
  have hq : 18553451 / 10000000 ≤ 1 + Real.exp (-(5 / 32)) := by linarith
  have hL : lamR (5 / 32) ≤ 3436 / 1000 := by
    unfold lamR
    have hpos : 0 < Real.sinh (5 / 32) * (1 + Real.exp (-(5 / 32))) := by positivity
    rw [div_le_iff₀ hpos]
    have := mul_le_mul hsh hq (by norm_num) (by linarith)
    nlinarith
  have hL0 : 0 < lamR (5 / 32) := lamR_pos _ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hDup hL0.le]

/-- The three `cothTail` logarithms at threshold `5/32`, half-width `21/100`. -/
theorem cothTail_combo_5_32_21 :
    -2 * cothTail (5 / 32) + cothTail (21 / 100) / 2 + cothTail (2 * (21 / 100)) / 2 ≤
      (-(12 / 100) - 9 * Real.log 2) / 2 := by
  obtain ⟨hbl, hbu⟩ := exp_neg_enc (21 / 100) (by norm_num) (by norm_num)
  obtain ⟨hal, hau⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at hbl hbu hal hau
  set a := Real.exp (-(5 / 32 : ℝ)) with ha
  set b := Real.exp (-(21 / 100 : ℝ)) with hb
  have hb2 : Real.exp (-(2 * (21 / 100 : ℝ))) = b ^ 2 := by
    rw [hb, sq, ← Real.exp_add]; ring_nf
  unfold cothTail
  rw [hb2]
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  have hb21 : 0 < 1 - b ^ 2 := by nlinarith
  have hA : 0 < (1 + a) / (1 - a) := div_pos (by linarith) ha1
  have hB : 0 < (1 + b) / (1 - b) := div_pos (by linarith) hb1
  have hC : 0 < (1 + b ^ 2) / (1 - b ^ 2) := div_pos (by positivity) hb21
  set y := (1 + b) / (1 - b) * ((1 + b ^ 2) / (1 - b ^ 2)) * 2 ^ 9 /
    ((1 + a) / (1 - a)) ^ 4 with hy
  have hy0 : 0 < y := by positivity
  have hlogy : Real.log y = Real.log ((1 + b) / (1 - b)) + Real.log ((1 + b ^ 2) / (1 - b ^ 2))
      + 9 * Real.log 2 - 4 * Real.log ((1 + a) / (1 - a)) := by
    rw [hy, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul hB.ne' hC.ne', Real.log_pow, Real.log_pow]
    push_cast; ring
  have hN : (1 + b) * (1 + b ^ 2) * (1 - a) ^ 4 ≤
      (1 + 8105917 / 10000000) * (1 + (8105917 / 10000000 : ℝ) ^ 2) *
        (1 - 8553451 / 10000000) ^ 4 := by
    have h1 : (1 + b) * (1 + b ^ 2) ≤
        (1 + 8105917 / 10000000) * (1 + (8105917 / 10000000 : ℝ) ^ 2) := by
      apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by norm_num)
    have h2 : (1 - a) ^ 4 ≤ (1 - 8553451 / 10000000 : ℝ) ^ 4 :=
      pow_le_pow_left₀ ha1.le (by linarith) 4
    exact mul_le_mul h1 h2 (by positivity) (by norm_num)
  have hDn : (1 - 8105917 / 10000000) * (1 - (8105917 / 10000000 : ℝ) ^ 2) *
        (1 + 8553451 / 10000000) ^ 4 ≤ (1 - b) * (1 - b ^ 2) * (1 + a) ^ 4 := by
    have h1 : (1 - 8105917 / 10000000) * (1 - (8105917 / 10000000 : ℝ) ^ 2) ≤
        (1 - b) * (1 - b ^ 2) := by
      apply mul_le_mul (by linarith) (by nlinarith) (by norm_num) hb1.le
    have h2 : (1 + 8553451 / 10000000 : ℝ) ^ 4 ≤ (1 + a) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 4
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnum : 512 * ((1 + 8105917 / 10000000) * (1 + (8105917 / 10000000 : ℝ) ^ 2) *
        (1 - 8553451 / 10000000) ^ 4) ≤
      (88 / 100) * ((1 - 8105917 / 10000000) * (1 - (8105917 / 10000000 : ℝ) ^ 2) *
        (1 + 8553451 / 10000000) ^ 4) := by norm_num
  have hyle : y ≤ 88 / 100 := by
    have hy' : y = 512 * ((1 + b) * (1 + b ^ 2) * (1 - a) ^ 4) /
        ((1 - b) * (1 - b ^ 2) * (1 + a) ^ 4) := by
      rw [hy]; field_simp; ring
    rw [hy', div_le_iff₀ (by positivity)]
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [hlogy] at hlog
  linarith

/-- `bonusGain (5/32) (21/100) ≤ −1/50` (true value ≈ −0.0463). -/
theorem bonusGain_5_32_21_100 : bonusGain (5 / 32) (21 / 100) ≤ -(1 / 50) := by
  have hlam := lam_term_5_32_21
  have hcombo := cothTail_combo_5_32_21
  obtain ⟨-, hs⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  norm_num at hs
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  unfold bonusGain thrGain
  have e2 : ((5 : ℝ) / 32) / 2 = 5 / 64 := by norm_num
  rw [e2] at *
  nlinarith

theorem bonus_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (21 / 100) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 50) * energy g.1 := by
  have hlog : 2 * (21 / 100 : ℝ) < Real.log 2 := by linarith [log_two_lower]
  have hd := bonus_diagonal g (5 / 32) (21 / 100) a (by norm_num) (by norm_num) (by norm_num)
    hlog hw hm
  have hg := mul_le_mul_of_nonneg_right bonusGain_5_32_21_100 (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`21/100` class.** -/
theorem universal_on_bonus_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (21 / 100) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := bonus_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHBonusClassV13

#print axioms AEGIS.RHBonusClassV13.bonusGain_5_32_21_100
#print axioms AEGIS.RHBonusClassV13.bonus_coercive
#print axioms AEGIS.RHBonusClassV13.universal_on_bonus_class
