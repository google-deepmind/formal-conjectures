import RHGramExpansionV13
import RHGoldenPrimeWindowV1
import RestrictedWeilCriterionKernelBridgeV10
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — four-translate Weil positivity on the golden lattice `q = φ²`, V1.

* diagonal at half-width `r = 1/128` (`RHDyadicDiagonalV13.diagonal_lower`):
    `cothTail(1/64) ≥ e^{-1/32}·log 2 + 6 log 2`, so the floor `D128 > 17/10`;
* cross terms at gaps `k·log q`, `k = 1, 2, 3`: prime-power-free windows
    (`RHGoldenPrimeWindowV1.window_all`), so `‖B‖ ≤ E/100` (`RHRatioWindowV13`);
* Gershgorin on the `4 × 4` Gram form (`RHGramExpansionV13.gram_re_le`):
    every row has exactly three off-diagonal entries, row sum `= 3/100`.

Result: for every moment-zero packet `g` of log-half-width `1/128` and every
`z ∈ ℂ⁴`,

  Re RHS(Autocorr(Σ_{k<4} z_k · T_{k log q} g)) ≤ −(D128 − 3/100)·E·Σ‖z_k‖²,
  with `D128 − 3/100 > 167/100`,

hence the canonical zero quadratic is nonnegative on that four-parameter family.
A finite family; not `UniversalZeroQuadraticNonnegativeV10`; not RH.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex Finset
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGoldenFourPacketV1
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHRatioWindowV13
open AEGIS.RHGoldenPrimeWindowV1
open AEGIS.RHGramExpansionV13
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- The four translates `T_{k log q} g`, `k = 0..3`. -/
def translates (g : WeilCompactSmoothGV1) (i : Fin 4) : WeilCompactSmoothGV1 :=
  translatePacket g ((i : ℕ) * Real.log q)

/-- The four-parameter golden family. -/
def fourPacket (g : WeilCompactSmoothGV1) (z : Fin 4 → ℂ) : WeilCompactSmoothGV1 :=
  packetSum z (translates g)

/-- The diagonal floor at half-width `1/128`. -/
def D128 : ℝ := cothTail (2 * (1 / 128)) - diagonalKappaV21 - (1 / 128) * Real.exp (1 / 64 : ℝ)

theorem D128_gt : (17 / 10 : ℝ) < D128 := by
  unfold D128 diagonalKappaV21
  have ht := cothTail_ge_below_32 (2 * (1 / 128)) (by norm_num) (by norm_num)
  have he32 : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 32 : ℝ))]
  have hlog : Real.log (1 / 32) - Real.log (2 * (1 / 128)) = Real.log 2 := by
    rw [show (1 / 32 : ℝ) = 2 ^ (-(5 : ℤ)) by norm_num,
      show (2 * (1 / 128) : ℝ) = 2 ^ (-(6 : ℤ)) by norm_num, Real.log_zpow, Real.log_zpow]
    push_cast; ring
  rw [hlog] at ht
  have hl2 := log_two_lower
  have hl2' := log_two_upper
  have hpi := log_four_pi_upper
  have hg := euler_mascheroni_upper
  have he64 := exp_one_over_64_upper
  nlinarith [mul_le_mul_of_nonneg_right he32 (by linarith : (0 : ℝ) ≤ Real.log 2)]

/-- Every translate keeps half-width `1/128` (recentred). -/
theorem translates_halfWidth (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (i : Fin 4) :
    HalfWidthAt (translates g i) (1 / 128) (a + (i : ℕ) * Real.log q) := by
  have hs := translate_logSupportIn g ((i : ℕ) * Real.log q) (a - 1 / 128) (a + 1 / 128) hw
  unfold translates HalfWidthAt
  convert hs using 1 <;> ring

theorem translates_diag (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (i : Fin 4) :
    D128 * energy g.1 ≤ -(B (translates g i) (translates g i)).re := by
  have h := diagonal_lower (translates g i) (1 / 128) (a + (i : ℕ) * Real.log q)
    (by norm_num) (by norm_num) (translates_halfWidth g a hw i)
  unfold translates at h ⊢
  rw [translate_energy] at h
  unfold D128
  linarith

/-- Cross ceilings: `1/100` at every golden gap `1..3`. -/
theorem translates_cross (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (hm : WeilMomentConditionsV1 g)
    (i j : Fin 4) (hij : i ≠ j) :
    ‖B (translates g i) (translates g j)‖ ≤ (fun _ : ℕ => (1 / 100 : ℝ)) (Nat.dist i j) * energy g.1 := by
  simp only []
  have key : ∀ i j : Fin 4, (i : ℕ) < j →
      ‖B (translates g i) (translates g j)‖ ≤ (1 / 100 : ℝ) * energy g.1 := by
    intro i j hlt
    have hk1 : 1 ≤ (j : ℕ) - i := by omega
    have hk3 : (j : ℕ) - i ≤ 3 := by have := j.isLt; omega
    have hgap : (j : ℕ) * Real.log q - (i : ℕ) * Real.log q = (((j : ℕ) - i : ℕ) : ℝ) * Real.log q := by
      rw [Nat.cast_sub hlt.le]; ring
    have hΛ := window_all ((j : ℕ) - i) hk1 hk3
    have hlq : Real.log 2 ≤ (j : ℕ) * Real.log q - (i : ℕ) * Real.log q := by
      rw [hgap]
      have hq := log_two_le_log_q
      have hk1' : (1 : ℝ) ≤ (((j : ℕ) - i : ℕ) : ℝ) := by exact_mod_cast hk1
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    unfold translates
    apply B_norm_le_arch_of_window_pair g (1 / 128) a _ _ (by norm_num) (by norm_num) hlq hw hm
    rw [hgap]
    exact hΛ
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · exact key i j h
  · rw [B_hermitian, RCLike.norm_conj]
    exact key j i h

/-- Each row has exactly three off-diagonal ceilings. -/
theorem translates_rowSum (i : Fin 4) :
    rowSum (fun _ : ℕ => (1 / 100 : ℝ)) i ≤ 3 / 100 := by
  unfold rowSum
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  norm_num

/-- **Coercivity on the golden four-parameter family.** -/
theorem fourPacket_coercive (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (hm : WeilMomentConditionsV1 g) (z : Fin 4 → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket g z))).re ≤
      -(D128 - 3 / 100) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  change (B (fourPacket g z) (fourPacket g z)).re ≤ _
  unfold fourPacket
  exact gram_re_le z (translates g) D128 (energy g.1) (3 / 100) (energy_nonnegative g.1)
    (fun _ => (1 / 100 : ℝ)) (fun _ => by norm_num)
    (translates_diag g a hw) (translates_cross g a hw hm) translates_rowSum

/-- The margin: `D128 − 3/100 > 167/100 ≥ 5/4`. -/
theorem margin_gt : (167 / 100 : ℝ) < D128 - 3 / 100 := by
  linarith [D128_gt]

theorem fourPacket_arithmetic_nonpositive (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (hm : WeilMomentConditionsV1 g) (z : Fin 4 → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (fourPacket g z))).re ≤ 0 := by
  have h := fourPacket_coercive g a hw hm z
  have hD := D128_gt
  have hE := energy_nonnegative g.1
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [mul_nonneg hE hS]

/-- Moments are preserved by packet sums. -/
theorem packetSum_preserves_moments {n : ℕ} (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (hgs : ∀ i, WeilMomentConditionsV1 (gs i)) :
    WeilMomentConditionsV1 (packetSum z gs) := by
  induction n with
  | zero => exact scalePacket_preserves_moments_v10 _ _ (hgs 0)
  | succ n ih =>
    exact addPacket_preserves_moments_v10 _ _
      (ih (fun i => z i.castSucc) (fun i => gs i.castSucc) (fun i => hgs _))
      (scalePacket_preserves_moments_v10 _ _ (hgs _))

theorem fourPacket_moments (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (z : Fin 4 → ℂ) : WeilMomentConditionsV1 (fourPacket g z) :=
  packetSum_preserves_moments z (translates g)
    (fun i => translate_preserves_moments g _ hm)

/-- **Weil positivity of the canonical zero quadratic on the golden four-parameter
family of every moment-zero packet of half-width `1/128`.** -/
theorem fourPacket_zero_quadratic_nonnegative (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 128) a) (hm : WeilMomentConditionsV1 g) (z : Fin 4 → ℂ) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 (fourPacket g z)) rho).re :=
  (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 (fourPacket g z)
      (fourPacket_moments g hm z)).mp (fourPacket_arithmetic_nonpositive g a hw hm z)

end AEGIS.RHGoldenFourPacketV1

#print axioms AEGIS.RHGoldenFourPacketV1.D128_gt
#print axioms AEGIS.RHGoldenFourPacketV1.fourPacket_coercive
#print axioms AEGIS.RHGoldenFourPacketV1.fourPacket_zero_quadratic_nonnegative
