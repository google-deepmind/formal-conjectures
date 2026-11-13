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

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Positivity

/-!
# Singular values and explicit Euclidean matrix norms

`Matrix.singularValue` uses the map between Euclidean spaces associated with a real matrix.
The index is zero-based: `singularValue A 0` is the largest singular value. The sequence is
zero from the matrix rank onward, including for rectangular or empty matrices.

`spectralNorm` is the largest singular value, `nuclearNorm` is their sum, and
`frobeniusNorm` is the square root of the sum of squared entries. These definitions do not
depend on the choice of a scoped matrix norm instance.

## References

* S. Axler, *Linear Algebra Done Right*, fourth edition, §7D.
* T. Armstrong, M. Weidner, and A. Zeleneev,
  [*Robust Estimation and Inference in Panels with Interactive Fixed Effects*]
  (https://arxiv.org/abs/2210.06639v4), §2.
-/

@[expose] public section

open scoped BigOperators

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The entrywise Euclidean inner product of real matrices. -/
def frobeniusInner (A B : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- The sum of the squared entries of a real matrix. -/
def frobeniusNormSq (A : Matrix m n ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The Frobenius norm, independent of scoped matrix norm instances. -/
noncomputable def frobeniusNorm (A : Matrix m n ℝ) : ℝ := Real.sqrt A.frobeniusNormSq

lemma frobeniusInner_comm (A B : Matrix m n ℝ) : A.frobeniusInner B = B.frobeniusInner A := by
  simp only [frobeniusInner, mul_comm]

lemma frobeniusInner_add_left (A B C : Matrix m n ℝ) :
    (A + B).frobeniusInner C = A.frobeniusInner C + B.frobeniusInner C := by
  simp [frobeniusInner, add_mul, Finset.sum_add_distrib]

lemma frobeniusInner_smul_left (c : ℝ) (A B : Matrix m n ℝ) :
    (c • A).frobeniusInner B = c * A.frobeniusInner B := by
  simp [frobeniusInner, mul_assoc, Finset.mul_sum]

@[simp] lemma frobeniusInner_zero_left (A : Matrix m n ℝ) :
    frobeniusInner 0 A = 0 := by simp [frobeniusInner]

@[simp] lemma frobeniusInner_zero_right (A : Matrix m n ℝ) :
    frobeniusInner A 0 = 0 := by simp [frobeniusInner]

lemma frobeniusInner_self (A : Matrix m n ℝ) : A.frobeniusInner A = A.frobeniusNormSq := by
  simp only [frobeniusInner, frobeniusNormSq, pow_two]

@[simp] lemma frobeniusInner_transpose (A B : Matrix m n ℝ) :
    A.transpose.frobeniusInner B.transpose = A.frobeniusInner B := by
  simp only [frobeniusInner, transpose_apply]
  rw [Finset.sum_comm]

lemma frobeniusNormSq_nonneg (A : Matrix m n ℝ) : 0 ≤ A.frobeniusNormSq := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A i j)

lemma frobeniusNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ A.frobeniusNorm := Real.sqrt_nonneg _

lemma sq_frobeniusNorm (A : Matrix m n ℝ) : A.frobeniusNorm ^ 2 = A.frobeniusNormSq :=
  Real.sq_sqrt (frobeniusNormSq_nonneg A)

@[simp] lemma frobeniusNormSq_transpose (A : Matrix m n ℝ) :
    A.transpose.frobeniusNormSq = A.frobeniusNormSq := by
  simp only [frobeniusNormSq, transpose_apply]
  rw [Finset.sum_comm]

@[simp] lemma frobeniusNorm_transpose (A : Matrix m n ℝ) :
    A.transpose.frobeniusNorm = A.frobeniusNorm := by
  simp only [frobeniusNorm, frobeniusNormSq_transpose]

@[simp] lemma frobeniusNormSq_zero : frobeniusNormSq (0 : Matrix m n ℝ) = 0 := by
  simp [frobeniusNormSq]

@[simp] lemma frobeniusNorm_zero : frobeniusNorm (0 : Matrix m n ℝ) = 0 := by
  simp [frobeniusNorm]

@[simp] lemma frobeniusNormSq_eq_zero_iff (A : Matrix m n ℝ) :
    A.frobeniusNormSq = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg (A i j))).1 h i (Finset.mem_univ i)
    exact sq_eq_zero_iff.1 ((Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ sq_nonneg (A i j))).1 hi j (Finset.mem_univ j))
  · rintro rfl
    exact frobeniusNormSq_zero

@[simp] lemma frobeniusNorm_eq_zero_iff (A : Matrix m n ℝ) : A.frobeniusNorm = 0 ↔ A = 0 := by
  rw [frobeniusNorm, Real.sqrt_eq_zero (frobeniusNormSq_nonneg A), frobeniusNormSq_eq_zero_iff]

variable [DecidableEq n]

/-- The zero-indexed singular values of a matrix acting between Euclidean spaces. -/
noncomputable def singularValue (A : Matrix m n ℝ) (i : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues i

/-- The Euclidean spectral norm, defined as the largest singular value. -/
noncomputable def spectralNorm (A : Matrix m n ℝ) : ℝ := A.singularValue 0

/-- The nuclear norm, the sum of all singular values. -/
noncomputable def nuclearNorm (A : Matrix m n ℝ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card n), A.singularValue i

lemma singularValue_nonneg (A : Matrix m n ℝ) (i : ℕ) : 0 ≤ A.singularValue i :=
  A.toEuclideanLin.singularValues_nonneg i

lemma singularValue_antitone (A : Matrix m n ℝ) : Antitone A.singularValue :=
  A.toEuclideanLin.singularValues_antitone

lemma rank_eq_finrank_range_toEuclideanLin (A : Matrix m n ℝ) :
    A.rank = Module.finrank ℝ A.toEuclideanLin.range :=
  A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun m ℝ).toBasis
    (EuclideanSpace.basisFun n ℝ).toBasis

lemma singularValue_eq_zero_iff (A : Matrix m n ℝ) (i : ℕ) :
    A.singularValue i = 0 ↔ A.rank ≤ i := by
  rw [rank_eq_finrank_range_toEuclideanLin]
  exact A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range

lemma singularValue_pos_iff (A : Matrix m n ℝ) (i : ℕ) :
    0 < A.singularValue i ↔ i < A.rank := by
  rw [rank_eq_finrank_range_toEuclideanLin]
  exact A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range

lemma singularValue_eq_zero_of_rank_le (A : Matrix m n ℝ) {i : ℕ} (h : A.rank ≤ i) :
    A.singularValue i = 0 := (singularValue_eq_zero_iff A i).2 h

lemma singularValue_eq_zero_of_card_width_le (A : Matrix m n ℝ) {i : ℕ}
    (h : Fintype.card n ≤ i) : A.singularValue i = 0 :=
  singularValue_eq_zero_of_rank_le A (A.rank_le_card_width.trans h)

lemma singularValue_eq_zero_of_card_height_le (A : Matrix m n ℝ) {i : ℕ}
    (h : Fintype.card m ≤ i) : A.singularValue i = 0 :=
  singularValue_eq_zero_of_rank_le A (A.rank_le_card_height.trans h)

@[simp] lemma singularValue_zero (i : ℕ) : singularValue (0 : Matrix m n ℝ) i = 0 := by
  simp [singularValue]

lemma spectralNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ A.spectralNorm :=
  A.singularValue_nonneg 0

lemma nuclearNorm_nonneg (A : Matrix m n ℝ) : 0 ≤ A.nuclearNorm :=
  Finset.sum_nonneg fun i _ ↦ A.singularValue_nonneg i

/-- Summing over the domain dimension includes exactly all nonzero singular values. -/
lemma nuclearNorm_eq_sum_range_rank (A : Matrix m n ℝ) :
    A.nuclearNorm = ∑ i ∈ Finset.range A.rank, A.singularValue i := by
  classical
  symm
  apply Finset.sum_subset (Finset.range_mono A.rank_le_card_width)
  intro i hi hnot
  exact singularValue_eq_zero_of_rank_le A (Nat.le_of_not_gt (by simpa using hnot))

@[simp] lemma spectralNorm_eq_zero_iff (A : Matrix m n ℝ) : A.spectralNorm = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hvalues : A.toEuclideanLin.singularValues = 0 := by
      ext i
      exact le_antisymm ((A.singularValue_antitone (Nat.zero_le i)).trans_eq h)
        (A.singularValue_nonneg i)
    exact Matrix.toEuclideanLin.injective (by
      simpa using A.toEuclideanLin.singularValues_eq_zero_iff.1 hvalues)
  · rintro rfl
    simp [spectralNorm]

lemma spectralNorm_pos_iff (A : Matrix m n ℝ) : 0 < A.spectralNorm ↔ A ≠ 0 := by
  rw [lt_iff_le_and_ne]
  simp only [spectralNorm_nonneg, true_and, ne_comm, ne_eq, spectralNorm_eq_zero_iff]

@[simp] lemma spectralNorm_zero : spectralNorm (0 : Matrix m n ℝ) = 0 := by
  simp [spectralNorm]

@[simp] lemma nuclearNorm_zero : nuclearNorm (0 : Matrix m n ℝ) = 0 := by
  simp [nuclearNorm]

end Matrix
