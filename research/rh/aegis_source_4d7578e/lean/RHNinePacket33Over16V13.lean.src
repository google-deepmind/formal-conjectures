import RHGramExpansionV13
import RHRatio33Over16V13
import RestrictedWeilCriterionKernelBridgeV10
import WeilAutocorrelationExplicitFormulaV10
import Mathlib.Tactic

/-!
AEGIS Ω — nine-translate Weil positivity on the `33/16` lattice, V13.

Assembly of the width pattern:

* diagonal at half-width `r = 1/256` (`RHDyadicDiagonalV13.diagonal_lower`):
    `E · (cothTail(1/128) − κ − (1/256)e^{1/64}) ≤ −Re B(Tg, Tg)`, and
    `cothTail(1/128) ≥ e^{-1/32}·log 4 + 6 log 2`, so the floor is `> 2.3 · E`;
* cross terms at gaps `k·log(33/16)`, `k = 1..8`: prime-power-free windows
    (`RHRatio33Over16V13.window_all`), so `‖B‖ ≤ E/100` (`RHRatioWindowV13`);
* Gershgorin on the `9 × 9` Toeplitz Gram form (`RHGramExpansionV13.gram_re_le`):
    row sum `≤ 2·8/100 = 4/25`.

Result: for every moment-zero packet `g` of log-half-width `1/256` and every
`z ∈ ℂ⁹`,

  Re RHS(Autocorr(Σ_{k<9} z_k · T_{k log(33/16)} g)) ≤ −(D − 4/25)·E·Σ‖z_k‖² ≤ 0,

hence the canonical zero quadratic is nonnegative on that nine-parameter family.
A finite family; not `UniversalZeroQuadraticNonnegativeV10`; not RH.
AUTHORITY_EFFECT = NONE.
-/

open Set Complex Finset
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNinePacket33Over16V13
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilDisjointEnergyV2
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilThreeBlockAnalyticConstantsV21
open AEGIS.WeilDiagonalKernelReductionV21
open AEGIS.RHDyadicDiagonalV13
open AEGIS.RHRatioWindowV13
open AEGIS.RHRatio33Over16V13
open AEGIS.RHGramExpansionV13
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationExplicitFormulaV10

/-- The nine translates `T_{k log q} g`, `k = 0..8`. -/
def translates (g : WeilCompactSmoothGV1) (i : Fin 9) : WeilCompactSmoothGV1 :=
  translatePacket g ((i : ℕ) * Real.log q)

/-- The nine-parameter family. -/
def ninePacket (g : WeilCompactSmoothGV1) (z : Fin 9 → ℂ) : WeilCompactSmoothGV1 :=
  packetSum z (translates g)

/-- The diagonal floor at half-width `1/256`. -/
def D256 : ℝ := cothTail (2 * (1 / 256)) - diagonalKappaV21 - (1 / 256) * Real.exp (1 / 64 : ℝ)

theorem D256_gt : (23 / 10 : ℝ) < D256 := by
  unfold D256 diagonalKappaV21
  have ht := cothTail_ge_below_32 (2 * (1 / 256)) (by norm_num) (by norm_num)
  have he32 : (31 / 32 : ℝ) ≤ Real.exp (-(1 / 32 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(1 / 32 : ℝ))]
  have hlog : Real.log (1 / 32) - Real.log (2 * (1 / 256)) = 2 * Real.log 2 := by
    rw [show (1 / 32 : ℝ) = 2 ^ (-(5 : ℤ)) by norm_num,
      show (2 * (1 / 256) : ℝ) = 2 ^ (-(7 : ℤ)) by norm_num, Real.log_zpow, Real.log_zpow]
    push_cast; ring
  rw [hlog] at ht
  have hl2 := log_two_lower
  have hl2' := log_two_upper
  have hpi := log_four_pi_upper
  have hg := euler_mascheroni_upper
  have he64 := exp_one_over_64_upper
  nlinarith [mul_le_mul_of_nonneg_right he32 (by linarith : (0 : ℝ) ≤ 2 * Real.log 2)]

/-- Every translate keeps half-width `1/256` (recentred) and the energy. -/
theorem translates_halfWidth (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (i : Fin 9) :
    HalfWidthAt (translates g i) (1 / 256) (a + (i : ℕ) * Real.log q) := by
  have hs := translate_logSupportIn g ((i : ℕ) * Real.log q) (a - 1 / 256) (a + 1 / 256) hw
  unfold translates HalfWidthAt
  convert hs using 1 <;> ring

theorem translates_diag (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (i : Fin 9) :
    D256 * energy g.1 ≤ -(B (translates g i) (translates g i)).re := by
  have h := diagonal_lower (translates g i) (1 / 256) (a + (i : ℕ) * Real.log q)
    (by norm_num) (by norm_num) (translates_halfWidth g a hw i)
  unfold translates at h ⊢
  rw [translate_energy] at h
  unfold D256
  linarith

/-- Cross ceilings: `1/100` at every gap `1..8`. -/
theorem translates_cross (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (hm : WeilMomentConditionsV1 g)
    (i j : Fin 9) (hij : i ≠ j) :
    ‖B (translates g i) (translates g j)‖ ≤ (fun _ : ℕ => (1 / 100 : ℝ)) (Nat.dist i j) * energy g.1 := by
  simp only []
  -- reduce to i < j by hermitian symmetry
  have key : ∀ i j : Fin 9, (i : ℕ) < j →
      ‖B (translates g i) (translates g j)‖ ≤ (1 / 100 : ℝ) * energy g.1 := by
    intro i j hlt
    have hk1 : 1 ≤ (j : ℕ) - i := by omega
    have hk8 : (j : ℕ) - i ≤ 8 := by have := j.isLt; omega
    have hgap : (j : ℕ) * Real.log q - (i : ℕ) * Real.log q = (((j : ℕ) - i : ℕ) : ℝ) * Real.log q := by
      rw [Nat.cast_sub hlt.le]; ring
    have hΛ := window_all ((j : ℕ) - i) hk1 hk8
    have hlq : Real.log 2 ≤ (j : ℕ) * Real.log q - (i : ℕ) * Real.log q := by
      rw [hgap]
      have hq := log_two_le_log_q
      have hk1' : (1 : ℝ) ≤ (((j : ℕ) - i : ℕ) : ℝ) := by exact_mod_cast hk1
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    unfold translates
    apply B_norm_le_arch_of_window_pair g (1 / 256) a _ _ (by norm_num) (by norm_num) hlq hw hm
    rw [hgap]
    exact hΛ
  rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hij (Fin.ext h)) with h | h
  · exact key i j h
  · rw [B_hermitian, RCLike.norm_conj]
    exact key j i h

theorem translates_rowSum (i : Fin 9) :
    rowSum (fun _ : ℕ => (1 / 100 : ℝ)) i ≤ 4 / 25 := by
  have := rowSum_le (fun _ : ℕ => (1 / 100 : ℝ)) (fun _ => by norm_num) i
  simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul] at this
  norm_num at this
  linarith

/-- **Coercivity on the nine-parameter family.** -/
theorem ninePacket_coercive (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (hm : WeilMomentConditionsV1 g) (z : Fin 9 → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (ninePacket g z))).re ≤
      -(D256 - 4 / 25) * energy g.1 * ∑ i, ‖z i‖ ^ 2 := by
  change (B (ninePacket g z) (ninePacket g z)).re ≤ _
  unfold ninePacket
  exact gram_re_le z (translates g) D256 (energy g.1) (4 / 25) (energy_nonnegative g.1)
    (fun _ => (1 / 100 : ℝ)) (fun _ => by norm_num)
    (translates_diag g a hw) (translates_cross g a hw hm) translates_rowSum

theorem ninePacket_arithmetic_nonpositive (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (hm : WeilMomentConditionsV1 g) (z : Fin 9 → ℂ) :
    (WeilExplicitRightSideV1 (WeilAutocorrelationV1 (ninePacket g z))).re ≤ 0 := by
  have h := ninePacket_coercive g a hw hm z
  have hD := D256_gt
  have hE := energy_nonnegative g.1
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  nlinarith [mul_nonneg hE hS]

/-- Moments are preserved by the nine-parameter combination. -/
theorem packetSum_preserves_moments {n : ℕ} (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) (hgs : ∀ i, WeilMomentConditionsV1 (gs i)) :
    WeilMomentConditionsV1 (packetSum z gs) := by
  induction n with
  | zero => exact scalePacket_preserves_moments_v10 _ _ (hgs 0)
  | succ n ih =>
    exact addPacket_preserves_moments_v10 _ _
      (ih (fun i => z i.castSucc) (fun i => gs i.castSucc) (fun i => hgs _))
      (scalePacket_preserves_moments_v10 _ _ (hgs _))

theorem ninePacket_moments (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (z : Fin 9 → ℂ) : WeilMomentConditionsV1 (ninePacket g z) :=
  packetSum_preserves_moments z (translates g)
    (fun i => translate_preserves_moments g _ hm)

/-- **Weil positivity of the canonical zero quadratic on the nine-parameter
`33/16` family of every moment-zero packet of half-width `1/256`.** -/
theorem ninePacket_zero_quadratic_nonnegative (g : WeilCompactSmoothGV1) (a : ℝ)
    (hw : HalfWidthAt g (1 / 256) a) (hm : WeilMomentConditionsV1 g) (z : Fin 9 → ℂ) :
    0 ≤ (∑' rho : RiemannNontrivialZeroIndexV2,
          WeilZeroIndexSummandV1 (WeilAutocorrelationV1 (ninePacket g z)) rho).re :=
  (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 (ninePacket g z)
      (ninePacket_moments g hm z)).mp (ninePacket_arithmetic_nonpositive g a hw hm z)

end AEGIS.RHNinePacket33Over16V13

#print axioms AEGIS.RHNinePacket33Over16V13.D256_gt
#print axioms AEGIS.RHNinePacket33Over16V13.ninePacket_coercive
#print axioms AEGIS.RHNinePacket33Over16V13.ninePacket_zero_quadratic_nonnegative
