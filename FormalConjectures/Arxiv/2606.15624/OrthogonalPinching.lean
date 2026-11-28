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

public import FormalConjecturesUtil
public import FormalConjectures.Wikipedia.Hadamard

/-!
# Orthogonal averages for diagonal pinching

* J.-C. Bourin and E.-Y. Lee, *Averages over matrix unitary orbits and spectral order*,
  Lemma 4.1 and Question 4.8. [Paper](https://arxiv.org/abs/2606.15624)
* M. J. Colbrook, [Partial result on MI-08](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/20861716f61359d2cf24c5d34a22d612eb3108ab/matrix-inequalities-and-norms/MI-08/solution.pdf),
  Theorem 1.1.
-/

@[expose] public section

namespace Arxiv.«2606.15624»

open Matrix

/-- A single family of $q$ orthogonal similarities averages to the diagonal part of every real
$d \times d$ matrix. Multiplying the identity by $q>0$ clears the denominator. -/
def IsPinchingLength (d q : ℕ) : Prop :=
  0 < q ∧ ∃ U : Fin q → orthogonalGroup (Fin d) ℝ, ∀ X : Matrix (Fin d) (Fin d) ℝ,
    ∑ k, (U k).val * X * (U k).valᵀ = (q : ℝ) • diagonal X.diag

def orthogonal_pinching.answer (d : ℕ) : ℕ := sorry

/-- Bourin and Lee, Question 4.8. For each $d\geq 1$, what is the smallest number of fixed
orthogonal similarities whose average sends every real matrix to its diagonal part? -/
@[category research open, question value, AMS 15]
theorem orthogonal_pinching (d : ℕ) (hd : 0 < d) :
    IsLeast {q | IsPinchingLength d q} (orthogonal_pinching.answer d) := by
  sorry

/-- A positive length $q$ works exactly when a $q \times d$ sign matrix has orthogonal columns
(the fixed-family case of Colbrook's Theorem 1.1). -/
@[category research solved, AMS 15]
theorem isPinchingLength_iff_signMatrix {d q : ℕ} (hq : 0 < q) :
    IsPinchingLength d q ↔ ∃ H : Matrix (Fin q) (Fin d) ℝ,
      (∀ k i, H k i = 1 ∨ H k i = -1) ∧ Hᵀ * H = (q : ℝ) • 1 := by
  constructor
  · rintro ⟨_, U, hU⟩
    let H : Matrix (Fin q) (Fin d) ℝ := fun k i ↦ (U k).val i i
    have hGram : Hᵀ * H = (q : ℝ) • 1 := by
      ext i j
      have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M i j) (hU (single i j 1))
      have hsingle (M : Matrix (Fin d) (Fin d) ℝ) :
          (M * Matrix.single i j (1 : ℝ) * Mᵀ) i j = M i i * M j j := by
        rw [single_eq_single_vecMulVec_single, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]
        simp [vecMulVec_apply]
      simp only [Matrix.sum_apply, hsingle, Matrix.smul_apply, smul_eq_mul] at h
      simp only [Matrix.mul_apply, transpose_apply]
      by_cases hij : i = j <;> simpa [H, hij, one_apply] using h
    refine ⟨H, ?_, hGram⟩
    intro k i
    have hle (l : Fin q) : H l i ^ 2 ≤ 1 := by
      have hrow := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M i i)
        ((mem_orthogonalGroup_iff (Fin d) ℝ).mp (U l).property)
      have hnorm : ∑ j, (U l).val i j ^ 2 = 1 := by simpa [mul_apply, pow_two] using hrow
      exact (Finset.single_le_sum (fun j _ ↦ sq_nonneg ((U l).val i j))
        (Finset.mem_univ i)).trans_eq hnorm
    apply sq_eq_one_iff.mp
    apply (Finset.sum_eq_sum_iff_of_le (fun l _ ↦ hle l)).mp _ k (Finset.mem_univ k)
    simpa [mul_apply, pow_two] using congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M i i) hGram
  · rintro ⟨H, hs, hGram⟩
    let U (k : Fin q) : orthogonalGroup (Fin d) ℝ := ⟨diagonal (H k), by
      rw [mem_orthogonalGroup_iff, diagonal_transpose, diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [one_apply, hij, mul_self_eq_one_iff.mpr (hs k j)]⟩
    refine ⟨hq, U, fun X ↦ ?_⟩
    ext i j
    have hij := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M i j) hGram
    simp only [mul_apply, transpose_apply, Matrix.smul_apply, smul_eq_mul] at hij
    simp only [U, Matrix.sum_apply, diagonal_transpose, mul_diagonal, diagonal_mul,
      Matrix.smul_apply, smul_eq_mul]
    calc
      _ = (∑ k, H k i * H k j) * X i j := by simp [Finset.sum_mul, mul_right_comm]
      _ = _ := by rw [hij]; by_cases h : i = j <;> simp [h, one_apply]

/-- At least $d$ orthogonal similarities are needed in dimension $d$. -/
@[category API, AMS 15]
theorem le_of_isPinchingLength {d q : ℕ} (h : IsPinchingLength d q) : d ≤ q := by
  obtain ⟨H, _, hGram⟩ := (isPinchingLength_iff_signMatrix h.1).mp h
  have hq : (q : ℝ) ∈ nonZeroDivisors ℝ :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h.1.ne')
  have hr := congrArg Matrix.rank hGram
  rw [rank_transpose_mul_self, rank_smul_of_mem_nonZeroDivisors _ hq, rank_one, Fintype.card_fin] at hr
  simpa [hr] using H.rank_le_height

/-- The lower bound $q=d$ is attainable exactly in the dimensions admitting a Hadamard matrix. -/
@[category research solved, AMS 5 15]
theorem isPinchingLength_self_iff {d : ℕ} (hd : 0 < d) :
    IsPinchingLength d d ↔ ∃ H : Matrix (Fin d) (Fin d) ℝ, Hadamard.IsHadamard' H := by
  rw [isPinchingLength_iff_signMatrix hd]
  simp [Hadamard.IsHadamard', Nat.cast_smul_eq_nsmul]

/-- Restricting a sign matrix to fewer columns gives a pinching family in the smaller dimension. -/
@[category API, AMS 15]
theorem IsPinchingLength.of_le {d n q : ℕ} (h : IsPinchingLength d q) (hn : n ≤ d) :
    IsPinchingLength n q := by
  obtain ⟨H, hs, hGram⟩ := (isPinchingLength_iff_signMatrix h.1).mp h
  refine (isPinchingLength_iff_signMatrix h.1).mpr
    ⟨H.submatrix id (Fin.castLE hn), fun k i ↦ hs k _, ?_⟩
  ext i j
  have hij := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ ↦ M (Fin.castLE hn i) (Fin.castLE hn j))
    hGram
  simpa [mul_apply, one_apply] using hij

/-- In dimension at least three the length is four times the number of rows in which the
first three sign columns agree. -/
@[category API, AMS 15]
theorem IsPinchingLength.four_dvd {d q : ℕ} (h : IsPinchingLength d q) (hd : 3 ≤ d) : 4 ∣ q := by
  classical
  obtain ⟨H, hs, hGram⟩ := (isPinchingLength_iff_signMatrix h.1).mp (h.of_le hd)
  have horth (i j : Fin 3) (hij : i ≠ j) : ∑ k, H k i * H k j = 0 := by
    simpa [mul_apply, hij] using congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ ↦ M i j) hGram
  let S := Finset.univ.filter fun k ↦ H k 0 = H k 1 ∧ H k 0 = H k 2
  have hcount : (S.card : ℝ) * 4 = q := calc
    _ = ∑ k, (if H k 0 = H k 1 ∧ H k 0 = H k 2 then (1 : ℝ) else 0) * 4 := by
      rw [← Finset.sum_mul, Finset.sum_boole]
    _ = ∑ k, (1 + H k 0 * H k 1 + H k 0 * H k 2 + H k 1 * H k 2) := by
      apply Finset.sum_congr rfl
      intro k _
      rcases hs k 0 with h₀ | h₀ <;> rcases hs k 1 with h₁ | h₁ <;>
        rcases hs k 2 with h₂ | h₂ <;> norm_num [h₀, h₁, h₂]
    _ = _ := by
      simp [Finset.sum_add_distrib, horth 0 1 (by decide), horth 0 2 (by decide),
        horth 1 2 (by decide)]
  exact ⟨S.card, by exact_mod_cast (show (q : ℝ) = 4 * S.card by linarith)⟩

/-- The minimum is twelve for $9 \leq d \leq 12$. In particular, at $d=9$ it lies strictly
between $d$ and the next power of two, answering the second part of Question 4.8. -/
@[category research solved, AMS 15]
theorem orthogonal_pinching.variants.nine_to_twelve {d : ℕ} (hd : 9 ≤ d) (hd' : d ≤ 12) :
    IsLeast {q | IsPinchingLength d q} 12 := by
  have h12 : IsPinchingLength 12 12 := by
    apply (isPinchingLength_iff_signMatrix (by decide)).mpr
    refine ⟨Hadamard.H12, fun k i ↦ by simpa using Hadamard.isHadamard_H12.1 k i, ?_⟩
    rw [← Matrix.ext_iff]
    norm_num +decide [Fin.forall_fin_succ, Matrix.mul_apply, Fin.sum_univ_succ, Hadamard.H12,
      Matrix.one_apply]
  refine ⟨h12.of_le hd', fun q hq ↦ ?_⟩
  have hmin := le_of_isPinchingLength hq
  obtain ⟨k, hk⟩ := IsPinchingLength.four_dvd hq (by omega)
  omega

end Arxiv.«2606.15624»
