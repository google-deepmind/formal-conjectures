/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.LovaszTheta

/-!
# Sanity checks for `SimpleGraph.lovaszThetaFunction`
-/

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The Lovász theta function of a graph on an empty vertex type is $0$. -/
theorem lovaszThetaFunction_isEmpty [IsEmpty α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    lovaszThetaFunction G = 0 := by
  have hset : {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬G.Adj i j → A i j = 1)} = {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨A, hA, _, _, rfl⟩
      simp [Matrix.IsHermitian.maxEigenvalue]
    · rintro rfl
      refine ⟨0, Matrix.isHermitian_zero, fun i => IsEmpty.elim ‹_› i,
        fun i => IsEmpty.elim ‹_› i, ?_⟩
      simp [Matrix.IsHermitian.maxEigenvalue]
  rw [lovaszThetaFunction, hset, csInf_singleton]

lemma one_le_maxEigenvalue_of_diag_eq_one [Nonempty α] {A : Matrix α α ℝ}
    (hA : A.IsHermitian) (hdiag : ∀ i, A i i = 1) :
    1 ≤ hA.maxEigenvalue := by
  have htrace : (Fintype.card α : ℝ) = ∑ i, hA.eigenvalues i := by
    have h := hA.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag_apply, hdiag, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] at h
    exact h
  have hle : ∑ i : α, hA.eigenvalues i ≤ ∑ _i : α, hA.maxEigenvalue :=
    Finset.sum_le_sum fun i _ => le_ciSup (Finite.bddAbove_range _) i
  rw [← htrace, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
  have hpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  exact (le_mul_iff_one_le_right hpos).mp hle

lemma bddBelow_lovaszThetaSet (G : SimpleGraph α) [DecidableRel G.Adj] :
    BddBelow {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬G.Adj i j → A i j = 1)} := by
  by_cases hα : Nonempty α
  · refine ⟨1, ?_⟩
    rintro _ ⟨A, hA, hdiag, _, rfl⟩
    exact one_le_maxEigenvalue_of_diag_eq_one hA hdiag
  · rw [not_nonempty_iff] at hα
    refine ⟨0, ?_⟩
    rintro _ ⟨A, hA, _, _, rfl⟩
    simp [Matrix.IsHermitian.maxEigenvalue]

lemma nonempty_lovaszThetaSet (G : SimpleGraph α) [DecidableRel G.Adj] :
    {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
      (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬G.Adj i j → A i j = 1)}.Nonempty := by
  let J : Matrix α α ℝ := Matrix.of fun _ _ => 1
  have hJ : J.IsHermitian := by
    ext i j
    simp [J, Matrix.conjTranspose_apply]
  exact ⟨hJ.maxEigenvalue, J, hJ, fun _ => rfl, fun _ _ _ => rfl, rfl⟩

/-- The Lovász theta function of any nonempty graph is at least $1$. -/
theorem one_le_lovaszThetaFunction [Nonempty α] (G : SimpleGraph α) [DecidableRel G.Adj] :
    1 ≤ lovaszThetaFunction G := by
  apply le_csInf (nonempty_lovaszThetaSet G)
  rintro _ ⟨A, hA, hdiag, _, rfl⟩
  exact one_le_maxEigenvalue_of_diag_eq_one hA hdiag

/-- Adding edges to a graph can only decrease or preserve its Lovász theta function. -/
theorem lovaszThetaFunction_anti {G H : SimpleGraph α} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G ≤ H) :
    lovaszThetaFunction H ≤ lovaszThetaFunction G := by
  apply csInf_le_csInf (bddBelow_lovaszThetaSet H) (nonempty_lovaszThetaSet G)
  rintro _ ⟨A, hA, hdiag, hnonadj, rfl⟩
  exact ⟨A, hA, hdiag, fun i j hij => hnonadj i j (fun hG => hij (h hG)), rfl⟩

/-- The Lovász theta function of the complete graph $K_n$ ($n \ge 1$) is $1$. -/
theorem lovaszThetaFunction_top [Nonempty α] :
    lovaszThetaFunction (⊤ : SimpleGraph α) = 1 := by
  apply le_antisymm
  · have h1 : (1 : Matrix α α ℝ).IsHermitian := Matrix.isHermitian_one
    have hmem : h1.maxEigenvalue ∈ {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ)
        (hA : A.IsHermitian) (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬(⊤ : SimpleGraph α).Adj i j → A i j = 1)} := by
      refine ⟨1, h1, fun _ => by simp, fun i j hij => ?_, rfl⟩
      simp only [top_adj, ne_eq, not_not] at hij
      subst hij
      simp
    refine (csInf_le (bddBelow_lovaszThetaSet ⊤) hmem).trans ?_
    apply ciSup_le
    intro i
    have hmv := h1.mulVec_eigenvectorBasis i
    rw [Matrix.one_mulVec] at hmv
    by_contra! hgt
    have hzero : ⇑(h1.eigenvectorBasis i) = 0 := by
      ext k
      have hk := congr_fun hmv k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hk ⊢
      nlinarith
    exact h1.eigenvectorBasis.orthonormal.ne_zero i (by ext k; exact congr_fun hzero k)
  · exact one_le_lovaszThetaFunction ⊤

/-- The Lovász theta function of the edgeless graph $\overline{K_n}$ is $n$. -/
theorem lovaszThetaFunction_bot :
    lovaszThetaFunction (⊥ : SimpleGraph α) = Fintype.card α := by
  by_cases hα : Nonempty α
  · let J : Matrix α α ℝ := Matrix.of fun _ _ => 1
    have hJ : J.IsHermitian := by
      ext i j
      simp [J, Matrix.conjTranspose_apply]
    have hset : {(Matrix.IsHermitian.maxEigenvalue hA) | (A : Matrix α α ℝ) (hA : A.IsHermitian)
        (_ : ∀ i, A i i = 1) (_ : ∀ i j, ¬(⊥ : SimpleGraph α).Adj i j → A i j = 1)} = {hJ.maxEigenvalue} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨A, hA, _, hnonadj, rfl⟩
        have hAJ : A = J := by
          ext i j
          exact hnonadj i j (by simp)
        subst hAJ
        rfl
      · rintro rfl
        exact ⟨J, hJ, fun _ => rfl, fun _ _ _ => rfl, rfl⟩
    rw [lovaszThetaFunction, hset, csInf_singleton]
    have heig_dic : ∀ i : α, hJ.eigenvalues i = 0 ∨ hJ.eigenvalues i = Fintype.card α := by
      intro i
      let u : α → ℝ := ⇑(hJ.eigenvectorBasis i)
      let s : ℝ := ∑ m : α, u m
      have hmul : ∀ k : α, hJ.eigenvalues i * u k = s := by
        intro k
        have hk := congr_fun (hJ.mulVec_eigenvectorBasis i) k
        simp only [J, Matrix.mulVec, dotProduct, Matrix.of_apply, one_mul, Pi.smul_apply,
          smul_eq_mul] at hk
        exact hk.symm
      have hsum : hJ.eigenvalues i * s = (Fintype.card α : ℝ) * s := by
        calc hJ.eigenvalues i * s
            = ∑ k : α, hJ.eigenvalues i * u k := by rw [Finset.mul_sum]
          _ = ∑ _k : α, s := Finset.sum_congr rfl fun k _ => hmul k
          _ = (Fintype.card α : ℝ) * s := by simp [Finset.sum_const, nsmul_eq_mul]
      by_cases hs : s = 0
      · left
        have hzero : ∀ k, hJ.eigenvalues i * u k = 0 := fun k => by rw [hmul k, hs]
        by_contra hne
        have hu : u = 0 := by
          ext k
          exact (mul_eq_zero.mp (hzero k)).resolve_left hne
        exact hJ.eigenvectorBasis.orthonormal.ne_zero i (by ext k; exact congr_fun hu k)
      · right
        exact mul_right_cancel₀ hs hsum
    apply le_antisymm
    · apply ciSup_le
      intro i
      rcases heig_dic i with h0 | hcard
      · linarith [show (0 : ℝ) ≤ Fintype.card α by positivity]
      · linarith
    · have htrace : (Fintype.card α : ℝ) = ∑ i, hJ.eigenvalues i := by
        have h := hJ.trace_eq_sum_eigenvalues
        simp only [J, Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] at h
        exact h
      obtain ⟨i, hi⟩ : ∃ i : α, hJ.eigenvalues i = Fintype.card α := by
        by_contra! hall
        have hall0 : ∀ i, hJ.eigenvalues i = 0 := fun i =>
          (heig_dic i).resolve_right (hall i)
        have hpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
        simp only [hall0, Finset.sum_const_zero] at htrace
        linarith
      exact hi ▸ le_ciSup (Finite.bddAbove_range _) i
  · rw [not_nonempty_iff] at hα
    simp [lovaszThetaFunction_isEmpty]

/-- The Lovász theta function of any graph is at most its number of vertices. -/
theorem lovaszThetaFunction_le_card (G : SimpleGraph α) [DecidableRel G.Adj] :
    lovaszThetaFunction G ≤ Fintype.card α :=
  (lovaszThetaFunction_anti bot_le).trans_eq lovaszThetaFunction_bot

end SimpleGraph
