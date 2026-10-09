import RHHatCellsV13

/-!
AEGIS Ω — Weil positivity on the half-width-1/4 class via a positive-definite kernel, V13.

Certificate for `RHHatBudgetV13.hat_diagonal`: `h = 1/24`, `n = 25` integer weights `vCert` (a
Fejér–Riesz factor, scaled by `10³`, of an LP-optimal positive-definite sequence), `σ = 10⁻⁶`,
`λ = 11511/5000`, cap boundaries `t₁ = 1/6`, `t₂ = 1/4`.  The kernel condition holds on
`(0, 1/2]` by `Q_of_checks` (48 sub-cells), the kernel integrals are exact trapezoid sums of
the autocorrelation values `ρ_k`, and `hatGain(1/4) ≤ −1/20`.
Every moment-zero packet of log-half-width `≤ 1/4` (support `≤ 1/2`) has `Re RHS ≤ −E/20`
and a nonnegative canonical zero quadratic.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatClassV13
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHThresholdClassV13
open AEGIS.RHHatKernelV13
open AEGIS.RHHatBudgetV13
open AEGIS.RHHatCellsV13

/-- The integer weights. -/
def vCert : ℕ → ℝ
  | 0 => 16744
  | 1 => -14564
  | 2 => -4613
  | 3 => 18
  | 4 => 2259
  | 5 => 2485
  | 6 => 2017
  | 7 => 1277
  | 8 => 466
  | 9 => -161
  | 10 => -464
  | 11 => -1185
  | 12 => -1804
  | 13 => -12563
  | 14 => 17611
  | 15 => 2204
  | 16 => -1401
  | 17 => -1570
  | 18 => -1783
  | 19 => -1174
  | 20 => -330
  | 21 => 363
  | 22 => 912
  | 23 => 1295
  | 24 => 393
  | _ => 0

/-- The autocorrelation values `ρ_0 … ρ_12`. -/
def rv : ℕ → ℝ
  | 0 => 1020568922
  | 1 => -313710065
  | 2 => -146276871
  | 3 => -73995753
  | 4 => -34166359
  | 5 => -8793248
  | 6 => 8652075
  | 7 => 21648608
  | 8 => 31526390
  | 9 => 39587092
  | 10 => 46102215
  | 11 => 51739158
  | 12 => 56520729
  | _ => 0

/-- `λ`. -/
def lamC : ℝ := ((11511 : ℝ) / 5000)

/-- `σ = 10⁻⁶`. -/
def sigC : ℝ := 1 / 1000000

set_option maxHeartbeats 4000000 in
theorem rho_0 : rhoK 25 vCert 0 = 1020568922 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_1 : rhoK 25 vCert 1 = -313710065 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_2 : rhoK 25 vCert 2 = -146276871 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_3 : rhoK 25 vCert 3 = -73995753 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_4 : rhoK 25 vCert 4 = -34166359 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_5 : rhoK 25 vCert 5 = -8793248 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_6 : rhoK 25 vCert 6 = 8652075 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_7 : rhoK 25 vCert 7 = 21648608 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_8 : rhoK 25 vCert 8 = 31526390 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_9 : rhoK 25 vCert 9 = 39587092 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_10 : rhoK 25 vCert 10 = 46102215 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_11 : rhoK 25 vCert 11 = 51739158 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_12 : rhoK 25 vCert 12 = 56520729 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

theorem nodeV (k : ℕ) (hk : k ≤ 12) : hatK (1 / 24) 25 vCert ((k : ℝ) * (1 / 24)) = (1 / 24) * rv k := by
  rw [hatK_node _ (by norm_num)]
  interval_cases k <;> norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rv]

set_option maxHeartbeats 20000000 in
theorem checks_0 : ∀ m : ℕ, m < 48 → 0 ≤ checkF lamC sigC ((1 / 24) * rv (m / 4))
    ((1 / 24) * rv (m / 4 + 1)) (((m % 4 : ℕ) : ℝ) / (4 : ℕ))
    (((m % 4 + 1 : ℕ) : ℝ) / (4 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (4 : ℕ)) * (1 / 24)) := by
  intro m hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

theorem Q_all : ∀ u ∈ Ioc (0 : ℝ) (2 * (1 / 4)), 0 ≤ kernelQ lamC sigC (1 / 24) 25 vCert u := by
  have e : (2 : ℝ) * (1 / 4) = ((12 : ℕ) : ℝ) * (1 / 24) := by norm_num
  rw [e]
  apply Q_of_checks lamC sigC (1 / 24) 25 vCert 12 4 rv (by norm_num) (by norm_num [sigC])
    (by norm_num [lamC]) (by norm_num) (by norm_num) nodeV
  intro m hm
  exact checks_0 m (by omega)

theorem int_1 : (∫ u in Ioc (0 : ℝ) ((1 : ℝ) / 6), hatK (1 / 24) 25 vCert u) = ((-9062535 : ℝ) / 128) := by
  have h := hatK_run_integral (1 / 24) (by norm_num) 25 vCert 0 4
  rw [show (((0 : ℕ) : ℝ)) * (1 / 24) = (0 : ℝ) by norm_num,
    show (((0 + 4 : ℕ) : ℝ)) * (1 / 24) = ((1 : ℝ) / 6) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 24) (by norm_num : (0 : ℝ) < 1 / 24)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12]

theorem int_2 : (∫ u in Ioc (((1 : ℝ) / 6) : ℝ) ((1 : ℝ) / 4), hatK (1 / 24) 25 vCert u) = ((-10775195 : ℝ) / 288) := by
  have h := hatK_run_integral (1 / 24) (by norm_num) 25 vCert 4 2
  rw [show (((4 : ℕ) : ℝ)) * (1 / 24) = (((1 : ℝ) / 6) : ℝ) by norm_num,
    show (((4 + 2 : ℕ) : ℝ)) * (1 / 24) = ((1 : ℝ) / 4) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 24) (by norm_num : (0 : ℝ) < 1 / 24)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12]

theorem int_3 : (∫ u in Ioc (((1 : ℝ) / 4) : ℝ) ((1 : ℝ) / 2), hatK (1 / 24) 25 vCert u) = ((223189865 : ℝ) / 576) := by
  have h := hatK_run_integral (1 / 24) (by norm_num) 25 vCert 6 6
  rw [show (((6 : ℕ) : ℝ)) * (1 / 24) = (((1 : ℝ) / 4) : ℝ) by norm_num,
    show (((6 + 6 : ℕ) : ℝ)) * (1 / 24) = ((1 : ℝ) / 2) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 24) (by norm_num : (0 : ℝ) < 1 / 24)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12]

/-- `hatGain(1/4) ≤ −1/20`. -/
theorem gain_bound : hatGain (1 / 4) lamC sigC (1 / 24) (1 / 6) (1 / 4) 25 vCert ≤ -(1 / 20) := by
  unfold hatGain
  have e2 : (2 : ℝ) * (1 / 4) / 2 = 1 / 4 := by norm_num
  have e1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  have e3 : (1 / 6 : ℝ) / 2 = 1 / 12 := by norm_num
  have e4 : (1 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
  rw [e2, e1, e3, e4, int_1, int_2, int_3]
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  obtain ⟨yl, -⟩ := exp_neg_enc ((1 : ℝ) / 2) (by norm_num) (by norm_num)
  obtain ⟨y2, -⟩ := exp_neg_enc ((1 : ℝ) / 4) (by norm_num) (by norm_num)
  obtain ⟨y1, -⟩ := exp_neg_enc ((1 : ℝ) / 6) (by norm_num) (by norm_num)
  have cl := cT_lower ((1 : ℝ) / 2) _ 1 2 (by norm_num) yl (by norm_num) (by norm_num) (by norm_num)
  have c2 := cT_lower ((1 : ℝ) / 4) _ 1 3 (by norm_num) y2 (by norm_num) (by norm_num) (by norm_num)
  have c1 := cT_lower ((1 : ℝ) / 6) _ 2 7 (by norm_num) y1 (by norm_num) (by norm_num) (by norm_num)
  have s1 := sinh_lower ((1 : ℝ) / 12) (by norm_num) (by norm_num)
  have s2 := sinh_lower ((1 : ℝ) / 8) (by norm_num) (by norm_num)
  have s3 := sinh_lower ((1 : ℝ) / 4) (by norm_num) (by norm_num)
  unfold lamC sigC
  norm_num at cl c2 c1 s1 s2 s3 ⊢
  linarith

theorem hat_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (1 / 4) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 20) * energy g.1 := by
  have hd := hat_diagonal g (1 / 4) a lamC sigC (1 / 24) (1 / 6) (1 / 4) 25 vCert
    (by norm_num) (by norm_num) (by linarith [log_two_lower]) (by norm_num) (by norm_num [sigC])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hm Q_all
  have hg := mul_le_mul_of_nonneg_right gain_bound (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`1/4` class.** -/
theorem universal_on_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (1 / 4) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := hat_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHatClassV13

#print axioms AEGIS.RHHatClassV13.Q_all
#print axioms AEGIS.RHHatClassV13.gain_bound
#print axioms AEGIS.RHHatClassV13.hat_coercive
#print axioms AEGIS.RHHatClassV13.universal_on_class
