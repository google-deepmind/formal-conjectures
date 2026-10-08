import RHGramExpansionV13
import RHDyadicWindowV13
import RestrictedWeilCriterionKernelBridgeV10
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
AEGIS Ω — the dyadic tower, V13.

For every `N` there is a half-width `2^{-m}` at which the canonical zero
quadratic is nonnegative on the whole `(N+1)`-parameter family

  Σ_{j ≤ N} z_j · T_{j·log 2} g,   `g` moment-zero, log-half-width `2^{-m}`.

Ingredients, all kernel-checked earlier: the diagonal floor
`E·(cothTail(2r) − κ − r·e^{1/64})` with `cothTail_ge_below_32`; the dyadic gap
ceilings `(log 2·2^{-k/2} + 1/100)·E` (single dyadic sample per window once
`2r ≤ 2^{-(k+1)}`); the `n`-block Gram/Gershgorin bound with
`rowSum ≤ 2·Σ_{k=1}^{N} c_k`; and the geometric series `Σ 2^{-k/2} ≤ 2.42`.
The width `m := max 10 (N + 2)` works.  An unbounded tower of finite
verifications on a sparse lattice; not universality; not RH.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex Finset
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHDyadicTowerV13
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHDyadicWindowV13
open AEGIS.RHGramExpansionV13
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- Half-width `2^{-m}`. -/
def hw (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ m

theorem hw_pos (m : ℕ) : 0 < hw m := by unfold hw; positivity

theorem hw_le_1_64 (m : ℕ) (hm : 6 ≤ m) : hw m ≤ 1 / 64 := by
  unfold hw
  calc (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ 6 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    _ = 1 / 64 := by norm_num

/-- Single-sample condition at every gap `k ≤ N` once `m ≥ N + 2`. -/
theorem hw_single_sample (m N k : ℕ) (hk : k ≤ N) (hm : N + 2 ≤ m) :
    2 * hw m ≤ 1 / (2 : ℝ) ^ (k + 1) := by
  unfold hw
  have h1 : (2 : ℝ) * (1 / 2) ^ m = (1 / 2) ^ (m - 1) := by
    have hm1 : m = (m - 1) + 1 := by omega
    conv_lhs => rw [hm1]
    rw [pow_succ]; ring
  have h2 : (1 : ℝ) / 2 ^ (k + 1) = (1 / 2) ^ (k + 1) := by rw [one_div_pow]
  rw [h1, h2]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- The dyadic translates `T_{i·log 2} g`, `i = 0..N`. -/
def translates (N : ℕ) (g : WeilCompactSmoothGV1) (i : Fin (N + 1)) : WeilCompactSmoothGV1 :=
  translatePacket g ((i : ℕ) * Real.log 2)

/-- The `(N+1)`-parameter family. -/
def towerPacket (N : ℕ) (g : WeilCompactSmoothGV1) (z : Fin (N + 1) → ℂ) : WeilCompactSmoothGV1 :=
  packetSum z (translates N g)

/-- Diagonal floor at half-width `2^{-m}`. -/
def Dm (m : ℕ) : ℝ := cothTail (2 * hw m) - diagonalKappaV21 - hw m * Real.exp (1 / 64 : ℝ)

/-- Gap ceiling. -/
def cgap (k : ℕ) : ℝ := Real.log 2 * dyadicHalf k + 1 / 100

theorem cgap_nonneg (k : ℕ) : 0 ≤ cgap k := by
  unfold cgap
  have := mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (dyadicHalf_pos k).le
  linarith

/-! ### The numeric core -/

theorem log_two_hw (m : ℕ) : Real.log (2 * hw m) = (1 - (m : ℝ)) * Real.log 2 := by
  unfold hw
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_div (by norm_num) (by norm_num),
    Real.log_one]
  ring

theorem Dm_ge (m : ℕ) (hm : 6 ≤ m) :
    (31 / 32 : ℝ) * ((m : ℝ) - 6) * Real.log 2 + 6 * Real.log 2 - diagonalKappaV21 - 1 / 60 ≤ Dm m := by
  unfold Dm
  have hw2 : 2 * hw m ≤ 1 / 32 := by
    have := hw_le_1_64 m hm; linarith
  have ht := cothTail_ge_below_32 (2 * hw m) (by linarith [hw_pos m]) hw2
  have he32 : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 32 : ℝ))]
  have hlog : Real.log (1 / 32) - Real.log (2 * hw m) = ((m : ℝ) - 6) * Real.log 2 := by
    rw [log_two_hw, show (1 / 32 : ℝ) = 2 ^ (-(5 : ℤ)) by norm_num, Real.log_zpow]
    push_cast; ring
  rw [hlog] at ht
  have hm6 : (0 : ℝ) ≤ (m : ℝ) - 6 := by
    have : (6 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hl2 := log_two_lower
  have hsmall : hw m * Real.exp (1 / 64 : ℝ) ≤ 1 / 60 := by
    have h1 := hw_le_1_64 m hm
    have h2 := exp_one_over_64_upper
    have h0 := hw_pos m
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right he32 (mul_nonneg hm6 (by linarith : (0 : ℝ) ≤ Real.log 2))]

/-- `dyadicHalf k = q^k` with `q = e^{-log 2 / 2}`, `q² = 1/2`. -/
theorem dyadicHalf_eq_pow (k : ℕ) :
    dyadicHalf k = (Real.exp (-(Real.log 2) / 2)) ^ k := by
  unfold dyadicHalf
  rw [← Real.exp_nat_mul]
  congr 1; ring

theorem q_sq : (Real.exp (-(Real.log 2) / 2)) ^ 2 = 1 / 2 := by
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(Real.log 2) / 2) = -Real.log 2 by push_cast; ring,
    Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem q_le : Real.exp (-(Real.log 2) / 2) ≤ 7072 / 10000 := by
  have h := q_sq
  have hp := Real.exp_pos (-(Real.log 2) / 2)
  nlinarith

theorem sum_dyadicHalf_le (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, dyadicHalf k) ≤ 242 / 100 := by
  simp_rw [dyadicHalf_eq_pow]
  have hq0 : 0 ≤ Real.exp (-(Real.log 2) / 2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-(Real.log 2) / 2) < 1 := by linarith [q_le]
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := rfl
  rw [hIcc]
  have h := geom_sum_Ico_le_of_lt_one hq0 hq1 (m := 1) (n := N + 1)
  have hq := q_le
  calc (∑ i ∈ Finset.Ico 1 (N + 1), Real.exp (-(Real.log 2) / 2) ^ i)
      ≤ Real.exp (-(Real.log 2) / 2) ^ 1 / (1 - Real.exp (-(Real.log 2) / 2)) := h
    _ ≤ 242 / 100 := by
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith

theorem rowSum_bound (N : ℕ) (i : Fin (N + 1)) :
    rowSum cgap i ≤ 2 * (Real.log 2 * (242 / 100) + (N : ℝ) / 100) := by
  have h := rowSum_le cgap cgap_nonneg i
  have hsum : (∑ k ∈ Finset.Icc 1 N, cgap k) ≤ Real.log 2 * (242 / 100) + (N : ℝ) / 100 := by
    unfold cgap
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have := sum_dyadicHalf_le N
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hcard : (((N + 1 - 1 : ℕ) : ℝ)) = N := by simp
    rw [hcard]
    nlinarith [mul_le_mul_of_nonneg_left this hl]
  linarith

/-- The margin is positive once `m ≥ max 10 (N + 2)`. -/
theorem margin_pos (m N : ℕ) (hm10 : 10 ≤ m) (hmN : N + 2 ≤ m) :
    0 ≤ Dm m - 2 * (Real.log 2 * (242 / 100) + (N : ℝ) / 100) := by
  have hD := Dm_ge m (by omega)
  have hm10' : (10 : ℝ) ≤ m := by exact_mod_cast hm10
  have hmN' : (N : ℝ) + 2 ≤ m := by exact_mod_cast hmN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  unfold diagonalKappaV21 at hD
  have hl2 := log_two_lower
  have hl2' := log_two_upper
  have hpi := log_four_pi_upper
  have hg := euler_mascheroni_upper
  nlinarith

/-! ### Assembly -/

theorem translates_halfWidth (N m : ℕ) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hwg : HalfWidthAt g (hw m) a) (i : Fin (N + 1)) :
    HalfWidthAt (translates N g i) (hw m) (a + (i : ℕ) * Real.log 2) := by
  have hs := translate_logSupportIn g ((i : ℕ) * Real.log 2) (a - hw m) (a + hw m) hwg
  unfold translates HalfWidthAt
  convert hs using 1 <;> ring

theorem translates_diag (N m : ℕ) (hm : 6 ≤ m) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hwg : HalfWidthAt g (hw m) a) (i : Fin (N + 1)) :
    Dm m * energy g.1 ≤ -(B (translates N g i) (translates N g i)).re := by
  have h := diagonal_lower (translates N g i) (hw m) (a + (i : ℕ) * Real.log 2)
    (hw_pos m) (hw_le_1_64 m hm) (translates_halfWidth N m g a hwg i)
  unfold translates at h ⊢
  rw [translate_energy] at h
  unfold Dm
  linarith

theorem translates_cross (N m : ℕ) (hm : 6 ≤ m) (hmN : N + 2 ≤ m) (g : WeilCompactSmoothGV1) (a : ℝ)
    (hwg : HalfWidthAt g (hw m) a) (hmom : WeilMomentConditionsV1 g)
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    ‖B (translates N g i) (translates N g j)‖ ≤ cgap (Nat.dist i j) * energy g.1 := by
  have key : ∀ i j : Fin (N + 1), (i : ℕ) < j →
      ‖B (translates N g i) (translates N g j)‖ ≤ cgap ((j : ℕ) - i) * energy g.1 := by
    intro i j hlt
    have hk1 : 1 ≤ (j : ℕ) - i := by omega
    have hkN : (j : ℕ) - i ≤ N := by have := j.isLt; omega
    have hgap : (j : ℕ) * Real.log 2 - (i : ℕ) * Real.log 2 = (((j : ℕ) - i : ℕ) : ℝ) * Real.log 2 := by
      rw [Nat.cast_sub hlt.le]; ring
    unfold translates cgap
    exact gap_B_norm_bound_pair g (hw m) a ((j : ℕ) - i) hk1 (hw_pos m)
      (hw_single_sample m N _ hkN hmN) (hw_le_1_64 m hm) hwg hmom _ _ hgap
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · rw [Nat.dist_eq_sub_of_le h.le]
    exact key i j h
  · rw [Nat.dist_eq_sub_of_le_right h.le, B_hermitian, RCLike.norm_conj]
    exact key j i h

theorem tower_coercive (N m : ℕ) (hm10 : 10 ≤ m) (hmN : N + 2 ≤ m)
    (g : WeilCompactSmoothGV1) (a : ℝ) (hwg : HalfWidthAt g (hw m) a)
    (hmom : WeilMomentConditionsV1 g) (z : Fin (N + 1) → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (towerPacket N g z))).re ≤
      -(Dm m - 2 * (Real.log 2 * (242 / 100) + (N : ℝ) / 100)) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  change (B (towerPacket N g z) (towerPacket N g z)).re ≤ _
  unfold towerPacket
  exact gram_re_le z (translates N g) (Dm m) (energy g.1) _ (energy_nonnegative g.1)
    cgap cgap_nonneg (translates_diag N m (by omega) g a hwg)
    (translates_cross N m (by omega) hmN g a hwg hmom) (rowSum_bound N)

theorem tower_arithmetic_nonpositive (N m : ℕ) (hm10 : 10 ≤ m) (hmN : N + 2 ≤ m)
    (g : WeilCompactSmoothGV1) (a : ℝ) (hwg : HalfWidthAt g (hw m) a)
    (hmom : WeilMomentConditionsV1 g) (z : Fin (N + 1) → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (towerPacket N g z))).re ≤ 0 := by
  have h := tower_coercive N m hm10 hmN g a hwg hmom z
  have hmar := margin_pos m N hm10 hmN
  have hE := energy_nonnegative g.1
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [mul_nonneg (mul_nonneg hmar hE) hS]

theorem towerPacket_moments (N : ℕ) (g : WeilCompactSmoothGV1) (hmom : WeilMomentConditionsV1 g)
    (z : Fin (N + 1) → ℂ) : WeilMomentConditionsV1 (towerPacket N g z) := by
  unfold towerPacket
  induction N with
  | zero => exact scalePacket_preserves_moments_v10 _ _ (translate_preserves_moments g _ hmom)
  | succ n ih =>
    exact addPacket_preserves_moments_v10 _ _
      (ih (fun i => z i.castSucc)) (scalePacket_preserves_moments_v10 _ _ (translate_preserves_moments g _ hmom))

/-- **The dyadic tower**: for every `N`, at half-width `2^{-m}` with
`m = max 10 (N + 2)`, the canonical zero quadratic is nonnegative on the whole
`(N+1)`-parameter dyadic translate family of every moment-zero packet. -/
theorem dyadic_tower (N : ℕ) :
    ∃ m : ℕ, ∀ (g : WeilCompactSmoothGV1) (a : ℝ), HalfWidthAt g (hw m) a →
      WeilMomentConditionsV1 g → ∀ z : Fin (N + 1) → ℂ,
        0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
              WeilZeroIndexSummandV1 (WeilAutocorrelationV1 (towerPacket N g z)) rho).re := by
  refine ⟨max 10 (N + 2), fun g a hwg hmom z => ?_⟩
  exact (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 _
      (towerPacket_moments N g hmom z)).mp
    (tower_arithmetic_nonpositive N (max 10 (N + 2)) (le_max_left _ _) (le_max_right _ _)
      g a hwg hmom z)

end AEGIS.RHDyadicTowerV13

#print axioms AEGIS.RHDyadicTowerV13.margin_pos
#print axioms AEGIS.RHDyadicTowerV13.tower_coercive
#print axioms AEGIS.RHDyadicTowerV13.dyadic_tower
