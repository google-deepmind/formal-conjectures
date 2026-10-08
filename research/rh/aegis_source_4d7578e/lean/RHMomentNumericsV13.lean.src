import RHDyadicDiagonalV13
import WeilThreeBlockAnalyticConstantsV21
import WeilDiagonalKernelReductionV21
import Mathlib.Tactic

/-!
AEGIS Ω — a numerical value of the moment gain, V13.

Defines

  momentGain r = κ + cothTail (2r) − 2·cothTail r + (r/2)·e^{r/2} + 4(cosh(r/2) − 1),

with `κ = diagonalKappaV21 = log(4π) + γ` and
`cothTail w = log((1+e^{−w})/(1−e^{−w}))`, and proves the single numerical
inequality

  momentGain (1/8) ≤ −1/5

(true value ≈ −0.2806).  Proof: with `q = e^{−1/8}`, a fourth-order Taylor
enclosure of `q`, the algebraic identity
`cothTail(1/4) − 2·cothTail(1/8) = log((1+q²)(1−q)/(1+q)³)`, the bound
`(1+q²)(1−q)/(1+q)³ ≤ (201/200)/32`, `log(201/200) ≤ 1/200`, `log 2 > 693/1000`,
`e^{1/16} < 16/15`, `e^{−1/16} ≤ 16/17`, `log(4π) < 633/250`, `γ < 29/50`.

This is a pure real-number estimate; no Weil functional is involved.
Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHMomentNumericsV13
open AEGIS.RHDyadicDiagonalV13
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilThreeBlockAnalyticConstantsV21

/-- The moment gain at log-half-width `r`. -/
def momentGain (r : ℝ) : ℝ :=
  diagonalKappaV21 + cothTail (2 * r) - 2 * cothTail r + (r / 2) * Real.exp (r / 2)
    + 4 * (Real.cosh (r / 2) - 1)

/-- Fourth-order Taylor enclosure of `e^{-1/8}`. -/
theorem exp_neg_eighth_bounds :
    (1 - 1 / 8 + 1 / 128 - 1 / 3072 - 1 / 78643 : ℝ) ≤ Real.exp (-(1 / 8)) ∧
      Real.exp (-(1 / 8)) ≤ (1 - 1 / 8 + 1 / 128 - 1 / 3072 + 1 / 78643 : ℝ) := by
  have h := Real.exp_bound (x := -(1 / 8 : ℝ)) (by rw [abs_neg, abs_of_pos (by norm_num)]; norm_num)
    (n := 4) (by norm_num)
  have h' := abs_le.mp h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  obtain ⟨h1, h2⟩ := h'
  constructor <;> linarith

/-- `cothTail(1/4) − 2·cothTail(1/8) ≤ −5 log 2 + 1/200`. -/
theorem cothTail_combo_le :
    cothTail (2 * (1 / 8)) - 2 * cothTail (1 / 8) ≤ -(5 * Real.log 2) + 1 / 200 := by
  obtain ⟨hlo, hhi⟩ := exp_neg_eighth_bounds
  set q := Real.exp (-(1 / 8 : ℝ)) with hqdef
  have hq2 : Real.exp (-(2 * (1 / 8 : ℝ))) = q ^ 2 := by
    rw [hqdef, sq, ← Real.exp_add]; ring_nf
  have hqpos : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by linarith
  unfold cothTail
  rw [hq2]
  set X := (1 + q ^ 2) / (1 - q ^ 2) with hX
  set Y := (1 + q) / (1 - q) with hY
  have h1q : 0 < 1 - q := by linarith
  have h1q2 : 0 < 1 - q ^ 2 := by nlinarith
  have hXpos : 0 < X := div_pos (by positivity) h1q2
  have hYpos : 0 < Y := div_pos (by linarith) h1q
  -- polynomial core: 32 (1+q²)(1−q) ≤ c (1+q)³ with c = 201/200
  have hA : (1 + q ^ 2) * (1 - q) ≤
      (1 + (1 - 1 / 8 + 1 / 128 - 1 / 3072 + 1 / 78643 : ℝ) ^ 2) *
        (1 - (1 - 1 / 8 + 1 / 128 - 1 / 3072 - 1 / 78643 : ℝ)) := by
    apply mul_le_mul _ (by linarith) h1q.le (by positivity)
    nlinarith
  have hB : (1 + (1 - 1 / 8 + 1 / 128 - 1 / 3072 - 1 / 78643 : ℝ)) ^ 3 ≤ (1 + q) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hpoly : 32 * ((1 + q ^ 2) * (1 - q)) ≤ (201 / 200) * (1 + q) ^ 3 := by
    have hnum : 32 * ((1 + (1 - 1 / 8 + 1 / 128 - 1 / 3072 + 1 / 78643 : ℝ) ^ 2) *
        (1 - (1 - 1 / 8 + 1 / 128 - 1 / 3072 - 1 / 78643 : ℝ))) ≤
        (201 / 200) * (1 + (1 - 1 / 8 + 1 / 128 - 1 / 3072 - 1 / 78643 : ℝ)) ^ 3 := by
      norm_num
    nlinarith
  have hXY : X ≤ (201 / 200) * Y ^ 2 / 2 ^ 5 := by
    rw [hX, hY, div_pow, div_le_iff₀ h1q2]
    have hsq : (1 - q ^ 2) = (1 - q) * (1 + q) := by ring
    rw [hsq]
    have hpos2 : 0 < (1 - q) ^ 2 := by positivity
    rw [show (201 / 200 : ℝ) * ((1 + q) ^ 2 / (1 - q) ^ 2) / 2 ^ 5 * ((1 - q) * (1 + q))
        = (201 / 200) * (1 + q) ^ 3 / (32 * (1 - q)) by field_simp; ring]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hlog : Real.log X ≤ Real.log ((201 / 200) * Y ^ 2 / 2 ^ 5) :=
    Real.log_le_log hXpos hXY
  have hR : Real.log ((201 / 200) * Y ^ 2 / 2 ^ 5)
      = Real.log (201 / 200) + 2 * Real.log Y - 5 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hR] at hlog
  have hc : Real.log (201 / 200 : ℝ) ≤ 1 / 200 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 201 / 200)
    linarith
  linarith

theorem momentGain_eighth : momentGain (1 / 8) ≤ -(1 / 5) := by
  have hcombo := cothTail_combo_le
  have hhalf : (1 / 8 : ℝ) / 2 = 1 / 16 := by norm_num
  unfold momentGain
  rw [hhalf, Real.cosh_eq]
  have he : Real.exp (1 / 16 : ℝ) < 16 / 15 := exp_one_over_16_upper
  have he_pos : 0 < Real.exp (1 / 16 : ℝ) := Real.exp_pos _
  have hen : Real.exp (-(1 / 16 : ℝ)) ≤ 16 / 17 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (1 / 16 : ℝ)
    linarith
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 := log_two_lower
  nlinarith

end AEGIS.RHMomentNumericsV13

#print axioms AEGIS.RHMomentNumericsV13.momentGain_eighth
#print axioms AEGIS.RHMomentNumericsV13.cothTail_combo_le
#print axioms AEGIS.RHMomentNumericsV13.exp_neg_eighth_bounds
