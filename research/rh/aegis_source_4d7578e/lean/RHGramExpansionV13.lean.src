import WeilMixedAlgebraV2
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
AEGIS Ω — `n`-block Gram expansion of the Weil form and a Gershgorin bound, V13.

`WeilMixedAlgebraV2` gives `B` as a sesquilinear form on packets.  The tree only
ever expands three or four blocks by hand (`combo`, `combo4`).  This module
expands a `Fin (n+1)`-indexed combination `Σ zᵢ gᵢ` for every `n`, and proves

  Re B(Σ zᵢ gᵢ, Σ zᵢ gᵢ) ≤ −(D − S) · E · Σ ‖zᵢ‖²

from a diagonal floor `D·E ≤ −Re B(gᵢ,gᵢ)`, gap-indexed cross ceilings
`‖B(gᵢ,gⱼ)‖ ≤ c(dist i j)·E` (the Toeplitz structure: the ceiling depends only
on the gap), and a row-sum bound `Σ_{j≠i} c(dist i j) ≤ S`.
Pure algebra; nothing arithmetic.  AUTHORITY_EFFECT = NONE.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGramExpansionV13
open AEGIS.WeilMixedAlgebraV2

/-- `Σ zᵢ • gᵢ` over `Fin (n+1)`. -/
def packetSum : {n : ℕ} → (Fin (n + 1) → ℂ) → (Fin (n + 1) → WeilCompactSmoothGV1) →
    WeilCompactSmoothGV1
  | 0, z, gs => scalePacket (z 0) (gs 0)
  | n + 1, z, gs =>
      addPacket (packetSum (fun i => z i.castSucc) (fun i => gs i.castSucc))
        (scalePacket (z (Fin.last (n + 1))) (gs (Fin.last (n + 1))))

theorem B_packetSum_left {n : ℕ} (z : Fin (n + 1) → ℂ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (h : WeilCompactSmoothGV1) :
    B (packetSum z gs) h = ∑ i, z i * B (gs i) h := by
  induction n with
  | zero => simp [packetSum, B_scale_left]
  | succ n ih =>
    simp only [packetSum, B_add_left, B_scale_left, ih, Fin.sum_univ_castSucc]

theorem B_packetSum_right {n : ℕ} (h : WeilCompactSmoothGV1) (z : Fin (n + 1) → ℂ)
    (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    B h (packetSum z gs) = ∑ j, star (z j) * B h (gs j) := by
  induction n with
  | zero => simp [packetSum, B_scale_right]
  | succ n ih =>
    simp only [packetSum, B_add_right, B_scale_right, ih, Fin.sum_univ_castSucc]

/-- Full Gram expansion. -/
theorem B_packetSum {n : ℕ} (z : Fin (n + 1) → ℂ) (gs : Fin (n + 1) → WeilCompactSmoothGV1) :
    B (packetSum z gs) (packetSum z gs) =
      ∑ i, ∑ j, z i * star (z j) * B (gs i) (gs j) := by
  rw [B_packetSum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [B_packetSum_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem re_diag (z : ℂ) (w : ℂ) : (z * star z * w).re = ‖z‖ ^ 2 * w.re := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]

theorem re_offdiag_le (z w b : ℂ) (c E : ℝ) (hb : ‖b‖ ≤ c * E) (hcE : 0 ≤ c * E) :
    (z * star w * b).re ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 * (c * E) := by
  calc (z * star w * b).re ≤ ‖z * star w * b‖ := Complex.re_le_norm _
    _ = ‖z‖ * ‖w‖ * ‖b‖ := by simp only [norm_mul, norm_star]
    _ ≤ ‖z‖ * ‖w‖ * (c * E) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (‖z‖ ^ 2 + ‖w‖ ^ 2) / 2 * (c * E) := by
        apply mul_le_mul_of_nonneg_right _ hcE
        nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- Row sum of the gap ceilings around `i`. -/
def rowSum {n : ℕ} (c : ℕ → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ j ∈ (univ : Finset (Fin (n + 1))).erase i, c (Nat.dist i j)

/-- Swapping the two indices of an off-diagonal double sum. -/
theorem sum_erase_comm {n : ℕ} (F : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i, ∑ j ∈ univ.erase i, F i j) = ∑ j, ∑ i ∈ univ.erase j, F i j := by
  apply Finset.sum_comm'
  intro i j
  simp only [Finset.mem_univ, Finset.mem_erase, ne_eq, true_and, and_true]
  exact ⟨fun h => fun h' => h h'.symm, fun h => fun h' => h h'.symm⟩

/-- **Gershgorin bound for the Weil Gram form.** -/
theorem gram_re_le {n : ℕ} (z : Fin (n + 1) → ℂ) (gs : Fin (n + 1) → WeilCompactSmoothGV1)
    (D E S : ℝ) (hE : 0 ≤ E) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hdiag : ∀ i, D * E ≤ -(B (gs i) (gs i)).re)
    (hcross : ∀ i j, i ≠ j → ‖B (gs i) (gs j)‖ ≤ c (Nat.dist i j) * E)
    (hrow : ∀ i : Fin (n + 1), rowSum c i ≤ S) :
    (B (packetSum z gs) (packetSum z gs)).re ≤ -(D - S) * E * ∑ i, ‖z i‖ ^ 2 := by
  rw [B_packetSum, Complex.re_sum]
  simp_rw [Complex.re_sum]
  have hsplit : ∀ i : Fin (n + 1),
      (∑ j, (z i * star (z j) * B (gs i) (gs j)).re) =
        ‖z i‖ ^ 2 * (B (gs i) (gs i)).re +
        ∑ j ∈ univ.erase i, (z i * star (z j) * B (gs i) (gs j)).re := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), re_diag]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hdiagsum : (∑ i, ‖z i‖ ^ 2 * (B (gs i) (gs i)).re) ≤ ∑ i, ‖z i‖ ^ 2 * (-(D * E)) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    linarith [hdiag i]
  have hoff : (∑ i, ∑ j ∈ univ.erase i, (z i * star (z j) * B (gs i) (gs j)).re) ≤
      ∑ i, ∑ j ∈ univ.erase i, (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 * (c (Nat.dist i j) * E) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    exact re_offdiag_le _ _ _ _ _ (hcross i j hij) (mul_nonneg (hc _) hE)
  have hA : (∑ i, ∑ j ∈ univ.erase i, ‖z i‖ ^ 2 / 2 * (c (Nat.dist i j) * E)) =
      ∑ i, ‖z i‖ ^ 2 / 2 * (rowSum c i * E) := by
    apply Finset.sum_congr rfl
    intro i _
    unfold rowSum
    simp only [Finset.sum_mul, Finset.mul_sum]
  have hB : (∑ i, ∑ j ∈ univ.erase i, ‖z j‖ ^ 2 / 2 * (c (Nat.dist i j) * E)) =
      ∑ j, ‖z j‖ ^ 2 / 2 * (rowSum c j * E) := by
    rw [sum_erase_comm (fun i j => ‖z j‖ ^ 2 / 2 * (c (Nat.dist i j) * E))]
    apply Finset.sum_congr rfl
    intro j _
    unfold rowSum
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Nat.dist_comm]
  have hsym : (∑ i, ∑ j ∈ univ.erase i, (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 * (c (Nat.dist i j) * E)) =
      ∑ i, ‖z i‖ ^ 2 * (rowSum c i * E) := by
    have hsplit2 : ∀ i j : Fin (n + 1),
        (‖z i‖ ^ 2 + ‖z j‖ ^ 2) / 2 * (c (Nat.dist i j) * E) =
          ‖z i‖ ^ 2 / 2 * (c (Nat.dist i j) * E) + ‖z j‖ ^ 2 / 2 * (c (Nat.dist i j) * E) := by
      intro i j; ring
    simp_rw [hsplit2, Finset.sum_add_distrib]
    rw [hA, hB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrowsum : (∑ i, ‖z i‖ ^ 2 * (rowSum c i * E)) ≤ ∑ i, ‖z i‖ ^ 2 * (S * E) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hrow i) hE
  calc
    (∑ i, ‖z i‖ ^ 2 * (B (gs i) (gs i)).re) +
        ∑ i, ∑ j ∈ univ.erase i, (z i * star (z j) * B (gs i) (gs j)).re
        ≤ (∑ i, ‖z i‖ ^ 2 * (-(D * E))) + ∑ i, ‖z i‖ ^ 2 * (S * E) := by
          linarith [hdiagsum, hoff, hsym, hrowsum]
    _ = -(D - S) * E * ∑ i, ‖z i‖ ^ 2 := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

/-! ### Bounding the row sum by twice the one-sided gap series -/

theorem rowSum_le {n : ℕ} (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (i : Fin (n + 1)) :
    rowSum c i ≤ 2 * ∑ k ∈ Finset.Icc 1 n, c k := by
  unfold rowSum
  -- split into j < i and i < j
  have hsub : (univ : Finset (Fin (n + 1))).erase i =
      (univ.filter (fun j : Fin (n + 1) => (j : ℕ) < i)) ∪
      (univ.filter (fun j : Fin (n + 1) => (i : ℕ) < j)) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and,
      ne_eq, and_true]
    constructor
    · intro h
      rcases lt_or_gt_of_ne (fun h' : (j : ℕ) = i => h (Fin.ext h')) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr h1
    · rintro (h | h) <;> intro h' <;> subst h' <;> exact lt_irrefl _ h
  have hdisj : Disjoint (univ.filter (fun j : Fin (n + 1) => (j : ℕ) < i))
      (univ.filter (fun j : Fin (n + 1) => (i : ℕ) < j)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  rw [hsub, Finset.sum_union hdisj]
  -- left half: j < i, dist i j = i − j ∈ Icc 1 n, injective
  have hL : (∑ j ∈ univ.filter (fun j : Fin (n + 1) => (j : ℕ) < i), c (Nat.dist i j)) ≤
      ∑ k ∈ Finset.Icc 1 n, c k := by
    rw [← Finset.sum_image (f := c) (s := univ.filter (fun j : Fin (n + 1) => (j : ℕ) < i))
      (g := fun j => Nat.dist i j) ?_]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        rw [Nat.dist_eq_sub_of_le_right hj.le]
        simp only [Finset.mem_Icc]
        constructor
        · omega
        · have := i.isLt; have := j.isLt; omega
      · intro k _ _; exact hc k
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      dsimp only at hab
      rw [Nat.dist_eq_sub_of_le_right ha.le, Nat.dist_eq_sub_of_le_right hb.le] at hab
      exact Fin.ext (by omega)
  have hR : (∑ j ∈ univ.filter (fun j : Fin (n + 1) => (i : ℕ) < j), c (Nat.dist i j)) ≤
      ∑ k ∈ Finset.Icc 1 n, c k := by
    rw [← Finset.sum_image (f := c) (s := univ.filter (fun j : Fin (n + 1) => (i : ℕ) < j))
      (g := fun j => Nat.dist i j) ?_]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨j, hj, rfl⟩ := hk
        rw [Nat.dist_eq_sub_of_le hj.le]
        simp only [Finset.mem_Icc]
        constructor
        · omega
        · have := i.isLt; have := j.isLt; omega
      · intro k _ _; exact hc k
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      dsimp only at hab
      rw [Nat.dist_eq_sub_of_le ha.le, Nat.dist_eq_sub_of_le hb.le] at hab
      exact Fin.ext (by omega)
  linarith

end AEGIS.RHGramExpansionV13

#print axioms AEGIS.RHGramExpansionV13.B_packetSum
#print axioms AEGIS.RHGramExpansionV13.gram_re_le
#print axioms AEGIS.RHGramExpansionV13.rowSum_le
