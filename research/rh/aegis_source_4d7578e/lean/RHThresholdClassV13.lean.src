import RHThresholdGainV13
import WeilThreeBlockAnalyticConstantsV21
import Mathlib.Tactic

/-!
AEGIS Ω — Weil positivity on the half-width-1/5 class, V13.

`thrGain (5/32) (1/5) ≤ −1/100` (true value ≈ −0.0237; the kernel threshold sits at
`t = 5/32 ≈ 0.78·r`), hence every moment-zero packet whose logarithmic support has
half-width at most `1/5` (support length `≤ 2/5`) has `Re RHS ≤ −E/100` and a
nonnegative canonical zero quadratic.  This extends the half-cap class (`11/64`).

Numerics: fourth-order Taylor enclosures from `Real.exp_bound`; the three `cothTail`
logarithms are combined into `log(y) − 9 log 2` with
`y = 512·(1+b)(1+b²)(1−a)⁴ / ((1−b)(1−b²)(1+a)⁴)`, `a = e^{−5/32}`, `b = e^{−1/5}`,
and `log y ≤ y − 1 ≤ −3/100`.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHThresholdClassV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHMomentPiecesV13
open AEGIS.RHThresholdGainV13

/-- Fourth-order Taylor enclosure of `exp` on `[-1, 1]`. -/
theorem exp_enc (x : ℝ) (hx : |x| ≤ 1) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 - |x| ^ 5 / 100 ≤ Real.exp x ∧
      Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + |x| ^ 5 / 100 := by
  have h := Real.exp_bound hx (n := 5) (by norm_num)
  have h' := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  obtain ⟨h1, h2⟩ := h'
  constructor <;> linarith

theorem exp_pos_enc (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 100 ≤ Real.exp x ∧
      Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := by
  have h := exp_enc x (by rw [abs_of_pos hx0]; exact hx1)
  rwa [abs_of_pos hx0] at h

theorem exp_neg_enc (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 - x ^ 5 / 100 ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 - x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 100 := by
  have h := exp_enc (-x) (by rw [abs_neg, abs_of_pos hx0]; exact hx1)
  rw [abs_neg, abs_of_pos hx0] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> nlinarith

/-- The λ-term at threshold `5/32`, half-width `1/5`, is at most `−3/40`. -/
theorem lam_term_5_32 :
    lamR (5 / 32) * (2 * Real.sinh (1 / 5) + 2 * Real.sinh ((1 / 5) / 2)
      - 8 * Real.sinh ((5 / 32) / 2)) ≤ -(3 / 40) := by
  obtain ⟨-, hr⟩ := exp_pos_enc (1 / 5) (by norm_num) (by norm_num)
  obtain ⟨hrn, -⟩ := exp_neg_enc (1 / 5) (by norm_num) (by norm_num)
  obtain ⟨-, hh⟩ := exp_pos_enc (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨hhn, -⟩ := exp_neg_enc (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨hs, -⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, hsn⟩ := exp_neg_enc (5 / 64) (by norm_num) (by norm_num)
  obtain ⟨-, ht⟩ := exp_pos_enc (5 / 32) (by norm_num) (by norm_num)
  obtain ⟨htn, htn'⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at hr hrn hh hhn hs hsn ht htn htn'
  have e1 : ((1 : ℝ) / 5) / 2 = 1 / 10 := by norm_num
  have e2 : ((5 : ℝ) / 32) / 2 = 5 / 64 := by norm_num
  rw [e1, e2]
  set D := 2 * Real.sinh (1 / 5) + 2 * Real.sinh (1 / 10) - 8 * Real.sinh (5 / 64) with hD
  have hDup : D ≤ -(22 / 1000) := by
    rw [hD, Real.sinh_eq, Real.sinh_eq, Real.sinh_eq]
    linarith
  have hsh : Real.sinh (5 / 32) ≤ 15688675 / 100000000 := by
    rw [Real.sinh_eq]; linarith
  have hsh0 : 0 < Real.sinh (5 / 32) := Real.sinh_pos_iff.mpr (by norm_num)
  have hq : 1 + Real.exp (-(5 / 32)) ≤ 18553471 / 10000000 := by linarith
  have hq0 : 0 < 1 + Real.exp (-(5 / 32)) := by positivity
  have hL : (3435 : ℝ) / 1000 ≤ lamR (5 / 32) := by
    unfold lamR
    rw [le_div_iff₀ (mul_pos hsh0 hq0)]
    have := mul_le_mul hsh hq hq0.le (by norm_num)
    nlinarith
  have hL0 : 0 < lamR (5 / 32) := lamR_pos _ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_left hDup hL0.le]

/-- The three `cothTail` logarithms at threshold `5/32`, half-width `1/5`. -/
theorem cothTail_combo_5_32 :
    -2 * cothTail (5 / 32) + cothTail (1 / 5) / 2 + cothTail (2 * (1 / 5)) / 2 ≤
      (-(3 / 100) - 9 * Real.log 2) / 2 := by
  obtain ⟨hbl, hbu⟩ := exp_neg_enc (1 / 5) (by norm_num) (by norm_num)
  obtain ⟨hal, hau⟩ := exp_neg_enc (5 / 32) (by norm_num) (by norm_num)
  norm_num at hbl hbu hal hau
  set a := Real.exp (-(5 / 32 : ℝ)) with ha
  set b := Real.exp (-(1 / 5 : ℝ)) with hb
  have hb2 : Real.exp (-(2 * (1 / 5 : ℝ))) = b ^ 2 := by
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
  -- numerator and denominator enclosures
  have hN : (1 + b) * (1 + b ^ 2) * (1 - a) ^ 4 ≤
      (1 + 8187366 / 10000000) * (1 + (8187366 / 10000000 : ℝ) ^ 2) *
        (1 - 8553451 / 10000000) ^ 4 := by
    have h1 : (1 + b) * (1 + b ^ 2) ≤
        (1 + 8187366 / 10000000) * (1 + (8187366 / 10000000 : ℝ) ^ 2) := by
      apply mul_le_mul (by linarith) (by nlinarith) (by positivity) (by norm_num)
    have h2 : (1 - a) ^ 4 ≤ (1 - 8553451 / 10000000 : ℝ) ^ 4 :=
      pow_le_pow_left₀ ha1.le (by linarith) 4
    exact mul_le_mul h1 h2 (by positivity) (by norm_num)
  have hDn : (1 - 8187366 / 10000000) * (1 - (8187366 / 10000000 : ℝ) ^ 2) *
        (1 + 8553451 / 10000000) ^ 4 ≤ (1 - b) * (1 - b ^ 2) * (1 + a) ^ 4 := by
    have h1 : (1 - 8187366 / 10000000) * (1 - (8187366 / 10000000 : ℝ) ^ 2) ≤
        (1 - b) * (1 - b ^ 2) := by
      apply mul_le_mul (by linarith) (by nlinarith) (by norm_num) hb1.le
    have h2 : (1 + 8553451 / 10000000 : ℝ) ^ 4 ≤ (1 + a) ^ 4 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 4
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hnum : 512 * ((1 + 8187366 / 10000000) * (1 + (8187366 / 10000000 : ℝ) ^ 2) *
        (1 - 8553451 / 10000000) ^ 4) ≤
      (97 / 100) * ((1 - 8187366 / 10000000) * (1 - (8187366 / 10000000 : ℝ) ^ 2) *
        (1 + 8553451 / 10000000) ^ 4) := by norm_num
  have hyle : y ≤ 97 / 100 := by
    have hy' : y = 512 * ((1 + b) * (1 + b ^ 2) * (1 - a) ^ 4) /
        ((1 - b) * (1 - b ^ 2) * (1 + a) ^ 4) := by
      rw [hy]; field_simp; ring
    rw [hy', div_le_iff₀ (by positivity)]
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [hlogy] at hlog
  linarith

/-- `thrGain (5/32) (1/5) ≤ −1/100` (true value ≈ −0.0237). -/
theorem thrGain_5_32_one_fifth : thrGain (5 / 32) (1 / 5) ≤ -(1 / 100) := by
  have hlam := lam_term_5_32
  have hcombo := cothTail_combo_5_32
  obtain ⟨-, hs⟩ := exp_pos_enc (5 / 64) (by norm_num) (by norm_num)
  norm_num at hs
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  unfold thrGain
  have e2 : ((5 : ℝ) / 32) / 2 = 5 / 64 := by norm_num
  rw [e2] at *
  nlinarith

theorem threshold_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (1 / 5) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 100) * energy g.1 := by
  have hlog : 2 * (1 / 5 : ℝ) < Real.log 2 := by linarith [log_two_lower]
  have hd := threshold_diagonal g (5 / 32) (1 / 5) a (by norm_num) (by norm_num) hlog hw hm
  have hg := mul_le_mul_of_nonneg_right thrGain_5_32_one_fifth (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`1/5` class.** -/
theorem universal_on_one_fifth_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (1 / 5) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := threshold_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHThresholdClassV13

#print axioms AEGIS.RHThresholdClassV13.thrGain_5_32_one_fifth
#print axioms AEGIS.RHThresholdClassV13.threshold_coercive
#print axioms AEGIS.RHThresholdClassV13.universal_on_one_fifth_class
