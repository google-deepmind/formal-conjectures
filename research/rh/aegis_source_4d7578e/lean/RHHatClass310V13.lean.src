import RHHatCellsV13

/-!
AEGIS Ω — Weil positivity on the half-width-3/10 class via a positive-definite kernel, V13.

Certificate for `RHHatBudgetV13.hat_diagonal`: `h = 1/40`, `n = 49` integer weights `vCert` (a
Fejér–Riesz factor, scaled by `10³`, of an LP-optimal positive-definite sequence), `σ = 10⁻⁶`,
`λ = 21279/10000`, cap boundaries `t₁ = 1/5`, `t₂ = 3/10`.  The kernel condition holds on
`(0, 3/5]` by `Q_of_checks` (192 sub-cells), the kernel integrals are exact trapezoid sums of
the autocorrelation values `ρ_k`, and `hatGain(3/10) ≤ −1/50`.
Every moment-zero packet of log-half-width `≤ 3/10` (support `≤ 3/5`) has `Re RHS ≤ −E/50`
and a nonnegative canonical zero quadratic.  Not RH.  AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHHatClass310V13
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
  | 0 => 40195
  | 1 => -26163
  | 2 => -12788
  | 3 => -8173
  | 4 => -1670
  | 5 => 945
  | 6 => 1409
  | 7 => 2465
  | 8 => 2830
  | 9 => 2374
  | 10 => 2102
  | 11 => 1736
  | 12 => 1099
  | 13 => 631
  | 14 => 201
  | 15 => -233
  | 16 => -529
  | 17 => -754
  | 18 => -898
  | 19 => -981
  | 20 => -1111
  | 21 => -803
  | 22 => -200
  | 23 => -3631
  | 24 => -2748
  | 25 => -29215
  | 26 => 34751
  | 27 => 11103
  | 28 => -875
  | 29 => 1517
  | 30 => -711
  | 31 => -3092
  | 32 => -2475
  | 33 => -2156
  | 34 => -2229
  | 35 => -1595
  | 36 => -986
  | 37 => -621
  | 38 => -87
  | 39 => 305
  | 40 => 636
  | 41 => 868
  | 42 => 939
  | 43 => 1068
  | 44 => 991
  | 45 => 799
  | 46 => 1090
  | 47 => 1385
  | 48 => -4518
  | _ => 0

/-- The autocorrelation values `ρ_0 … ρ_24`. -/
def rv : ℕ → ℝ
  | 0 => 4835886331
  | 1 => -1090666142
  | 2 => -566605415
  | 3 => -348916885
  | 4 => -231084557
  | 5 => -157700766
  | 6 => -107680331
  | 7 => -71407724
  | 8 => -43853028
  | 9 => -22173180
  | 10 => -4702202
  | 11 => 9813720
  | 12 => 22011004
  | 13 => 32367383
  | 14 => 41450868
  | 15 => 49401793
  | 16 => 56448424
  | 17 => 62736901
  | 18 => 68463897
  | 19 => 73641439
  | 20 => 78448948
  | 21 => 82799850
  | 22 => 86961856
  | 23 => 90784209
  | 24 => 94430010
  | _ => 0

/-- `λ`. -/
def lamC : ℝ := ((21279 : ℝ) / 10000)

/-- `σ = 10⁻⁶`. -/
def sigC : ℝ := 1 / 1000000

set_option maxHeartbeats 4000000 in
theorem rho_0 : rhoK 49 vCert 0 = 4835886331 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_1 : rhoK 49 vCert 1 = -1090666142 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_2 : rhoK 49 vCert 2 = -566605415 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_3 : rhoK 49 vCert 3 = -348916885 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_4 : rhoK 49 vCert 4 = -231084557 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_5 : rhoK 49 vCert 5 = -157700766 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_6 : rhoK 49 vCert 6 = -107680331 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_7 : rhoK 49 vCert 7 = -71407724 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_8 : rhoK 49 vCert 8 = -43853028 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_9 : rhoK 49 vCert 9 = -22173180 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_10 : rhoK 49 vCert 10 = -4702202 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_11 : rhoK 49 vCert 11 = 9813720 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_12 : rhoK 49 vCert 12 = 22011004 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_13 : rhoK 49 vCert 13 = 32367383 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_14 : rhoK 49 vCert 14 = 41450868 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_15 : rhoK 49 vCert 15 = 49401793 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_16 : rhoK 49 vCert 16 = 56448424 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_17 : rhoK 49 vCert 17 = 62736901 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_18 : rhoK 49 vCert 18 = 68463897 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_19 : rhoK 49 vCert 19 = 73641439 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_20 : rhoK 49 vCert 20 = 78448948 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_21 : rhoK 49 vCert 21 = 82799850 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_22 : rhoK 49 vCert 22 = 86961856 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_23 : rhoK 49 vCert 23 = 90784209 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

set_option maxHeartbeats 4000000 in
theorem rho_24 : rhoK 49 vCert 24 = 94430010 := by
  norm_num [rhoK, Finset.sum_range_succ, vCert]

theorem nodeV (k : ℕ) (hk : k ≤ 24) : hatK (1 / 40) 49 vCert ((k : ℝ) * (1 / 40)) = (1 / 40) * rv k := by
  rw [hatK_node _ (by norm_num)]
  interval_cases k <;> norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24, rv]

set_option maxHeartbeats 20000000 in
theorem checks_0 : ∀ m : ℕ, m < 48 → 0 ≤ checkF lamC sigC ((1 / 40) * rv (m / 8))
    ((1 / 40) * rv (m / 8 + 1)) (((m % 8 : ℕ) : ℝ) / (8 : ℕ))
    (((m % 8 + 1 : ℕ) : ℝ) / (8 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (8 : ℕ)) * (1 / 40)) := by
  intro m hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_1 : ∀ m : ℕ, 48 ≤ m → m < 96 → 0 ≤ checkF lamC sigC ((1 / 40) * rv (m / 8))
    ((1 / 40) * rv (m / 8 + 1)) (((m % 8 : ℕ) : ℝ) / (8 : ℕ))
    (((m % 8 + 1 : ℕ) : ℝ) / (8 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (8 : ℕ)) * (1 / 40)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_2 : ∀ m : ℕ, 96 ≤ m → m < 144 → 0 ≤ checkF lamC sigC ((1 / 40) * rv (m / 8))
    ((1 / 40) * rv (m / 8 + 1)) (((m % 8 : ℕ) : ℝ) / (8 : ℕ))
    (((m % 8 + 1 : ℕ) : ℝ) / (8 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (8 : ℕ)) * (1 / 40)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

set_option maxHeartbeats 20000000 in
theorem checks_3 : ∀ m : ℕ, 144 ≤ m → m < 192 → 0 ≤ checkF lamC sigC ((1 / 40) * rv (m / 8))
    ((1 / 40) * rv (m / 8 + 1)) (((m % 8 : ℕ) : ℝ) / (8 : ℕ))
    (((m % 8 + 1 : ℕ) : ℝ) / (8 : ℕ)) ((((m + 1 : ℕ) : ℝ) / (8 : ℕ)) * (1 / 40)) := by
  intro m hm0 hm
  interval_cases m <;> norm_num [checkF, rv, lamC, sigC, min_def]

theorem Q_all : ∀ u ∈ Ioc (0 : ℝ) (2 * (3 / 10)), 0 ≤ kernelQ lamC sigC (1 / 40) 49 vCert u := by
  have e : (2 : ℝ) * (3 / 10) = ((24 : ℕ) : ℝ) * (1 / 40) := by norm_num
  rw [e]
  apply Q_of_checks lamC sigC (1 / 40) 49 vCert 24 8 rv (by norm_num) (by norm_num [sigC])
    (by norm_num [lamC]) (by norm_num) (by norm_num) nodeV
  intro m hm
  by_cases h0 : m < 48
  · exact checks_0 m h0
  push Not at h0
  by_cases h1 : m < 96
  · exact checks_1 m (by omega) h1
  push Not at h1
  by_cases h2 : m < 144
  · exact checks_2 m (by omega) h2
  push Not at h2
  exact checks_3 m (by omega) (by omega)

theorem int_1 : (∫ u in Ioc (0 : ℝ) ((1 : ℝ) / 5), hatK (1 / 40) 49 vCert u) = ((-356090337 : ℝ) / 3200) := by
  have h := hatK_run_integral (1 / 40) (by norm_num) 49 vCert 0 8
  rw [show (((0 : ℕ) : ℝ)) * (1 / 40) = (0 : ℝ) by norm_num,
    show (((0 + 8 : ℕ) : ℝ)) * (1 / 40) = ((1 : ℝ) / 5) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 40) (by norm_num : (0 : ℝ) < 1 / 40)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24]

theorem int_2 : (∫ u in Ioc (((1 : ℝ) / 5) : ℝ) ((3 : ℝ) / 10), hatK (1 / 40) 49 vCert u) = ((-13991337 : ℝ) / 800) := by
  have h := hatK_run_integral (1 / 40) (by norm_num) 49 vCert 8 4
  rw [show (((8 : ℕ) : ℝ)) * (1 / 40) = (((1 : ℝ) / 5) : ℝ) by norm_num,
    show (((8 + 4 : ℕ) : ℝ)) * (1 / 40) = ((3 : ℝ) / 10) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 40) (by norm_num : (0 : ℝ) < 1 / 40)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24]

theorem int_3 : (∫ u in Ioc (((3 : ℝ) / 10) : ℝ) ((3 : ℝ) / 5), hatK (1 / 40) 49 vCert u) = ((31269043 : ℝ) / 64) := by
  have h := hatK_run_integral (1 / 40) (by norm_num) 49 vCert 12 12
  rw [show (((12 : ℕ) : ℝ)) * (1 / 40) = (((3 : ℝ) / 10) : ℝ) by norm_num,
    show (((12 + 12 : ℕ) : ℝ)) * (1 / 40) = ((3 : ℝ) / 5) by norm_num] at h
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hatK_node (1 / 40) (by norm_num : (0 : ℝ) < 1 / 40)]
  norm_num [rho_0, rho_1, rho_2, rho_3, rho_4, rho_5, rho_6, rho_7, rho_8, rho_9, rho_10, rho_11, rho_12, rho_13, rho_14, rho_15, rho_16, rho_17, rho_18, rho_19, rho_20, rho_21, rho_22, rho_23, rho_24]

/-- `hatGain(3/10) ≤ −1/50`. -/
theorem gain_bound : hatGain (3 / 10) lamC sigC (1 / 40) (1 / 5) (3 / 10) 49 vCert ≤ -(1 / 50) := by
  unfold hatGain
  have e2 : (2 : ℝ) * (3 / 10) / 2 = 3 / 10 := by norm_num
  have e1 : (2 : ℝ) * (3 / 10) = 3 / 5 := by norm_num
  have e3 : (1 / 5 : ℝ) / 2 = 1 / 10 := by norm_num
  have e4 : (3 / 10 : ℝ) / 2 = 3 / 20 := by norm_num
  rw [e2, e1, e3, e4, int_1, int_2, int_3]
  have hk : diagonalKappaV21 < 633 / 250 + 29 / 50 := by
    unfold diagonalKappaV21
    linarith [log_four_pi_upper, euler_mascheroni_upper]
  have hl2 : (6931471803 : ℝ) / 10000000000 < Real.log 2 :=
    lt_of_eq_of_lt (by norm_num) Real.log_two_gt_d9
  obtain ⟨yl, -⟩ := exp_neg_enc ((3 : ℝ) / 5) (by norm_num) (by norm_num)
  obtain ⟨y2, -⟩ := exp_neg_enc ((3 : ℝ) / 10) (by norm_num) (by norm_num)
  obtain ⟨y1, -⟩ := exp_neg_enc ((1 : ℝ) / 5) (by norm_num) (by norm_num)
  have cl := cT_lower ((3 : ℝ) / 5) _ 4 7 (by norm_num) yl (by norm_num) (by norm_num) (by norm_num)
  have c2 := cT_lower ((3 : ℝ) / 10) _ 3 8 (by norm_num) y2 (by norm_num) (by norm_num) (by norm_num)
  have c1 := cT_lower ((1 : ℝ) / 5) _ 4 13 (by norm_num) y1 (by norm_num) (by norm_num) (by norm_num)
  have s1 := sinh_lower ((1 : ℝ) / 10) (by norm_num) (by norm_num)
  have s2 := sinh_lower ((3 : ℝ) / 20) (by norm_num) (by norm_num)
  have s3 := sinh_lower ((3 : ℝ) / 10) (by norm_num) (by norm_num)
  unfold lamC sigC
  norm_num at cl c2 c1 s1 s2 s3 ⊢
  linarith

theorem hat_coercive (g : WeilCompactSmoothGV1) (a : ℝ) (hw : HalfWidthAt g (3 / 10) a)
    (hm : WeilMomentConditionsV1 g) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 g)).re ≤ -(1 / 50) * energy g.1 := by
  have hd := hat_diagonal g (3 / 10) a lamC sigC (1 / 40) (1 / 5) (3 / 10) 49 vCert
    (by norm_num) (by norm_num) (by linarith [log_two_lower]) (by norm_num) (by norm_num [sigC])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hw hm Q_all
  have hg := mul_le_mul_of_nonneg_right gain_bound (energy_nonnegative g.1)
  linarith

/-- **Weil positivity on the half-width-`3/10` class.** -/
theorem universal_on_class (a : ℝ) :
    ∀ g : WeilCompactSmoothGV1, HalfWidthAt g (3 / 10) a → WeilMomentConditionsV1 g →
      0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
            WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho).re := by
  intro g hw hm
  have hc := hat_coercive g a hw hm
  have hE := energy_nonnegative g.1
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp (by linarith)

end AEGIS.RHHatClass310V13

#print axioms AEGIS.RHHatClass310V13.Q_all
#print axioms AEGIS.RHHatClass310V13.gain_bound
#print axioms AEGIS.RHHatClass310V13.hat_coercive
#print axioms AEGIS.RHHatClass310V13.universal_on_class
