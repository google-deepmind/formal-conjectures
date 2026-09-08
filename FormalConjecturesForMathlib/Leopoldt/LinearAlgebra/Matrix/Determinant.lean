/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Minors of a matrix whose rows sum to zero

Let `A : Matrix m n R` be a matrix whose rows sum to zero, `∑ j, A i j = 0` for all `i`.
Deleting one column `a` and identifying the remaining columns with `m` through an equivalence
`e : m ≃ {j // j ≠ a}` gives the square minor `A.submatrix id fun k ↦ (e k : n)`. We show:

* `Matrix.det_submatrix_ne_eq_or_eq_neg`: the determinants of any two such minors agree up to
  sign, whichever column is deleted and whichever equivalence is used;
* `Matrix.det_submatrix_ne_ne_zero_iff`: over a field, such a minor is nonsingular if and only if
  `A` has full row rank `Fintype.card m`.

This is the argument showing that the regulator of a number field is well defined: the rows of
the matrix `(log |σ(ε_i)|)` sum to `log |N(ε_i)| = 0`, so the `r × r` minor obtained by deleting
any one embedding has the same determinant up to sign. See for instance [Washington,
*Introduction to Cyclotomic Fields*, §4.3 and §5.5].
-/

@[expose] public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n] [CommRing R]

omit [Fintype n] in
/-- Reindexing the columns of a matrix by two different equivalences gives determinants that
agree up to sign. -/
theorem det_submatrix_id_eq_or_eq_neg {β : Type*} (A : Matrix m n R) (v : β → n)
    (e₀ e₁ : m ≃ β) :
    (A.submatrix id fun k ↦ v (e₀ k)).det = (A.submatrix id fun k ↦ v (e₁ k)).det ∨
      (A.submatrix id fun k ↦ v (e₀ k)).det = -(A.submatrix id fun k ↦ v (e₁ k)).det := by
  have h : (A.submatrix id fun k ↦ v (e₀ k)) =
      (A.submatrix id fun k ↦ v (e₁ k)).submatrix id (e₀.trans e₁.symm) := by
    ext i k
    simp
  rw [h, det_permute']
  rcases Int.isUnit_eq_one_or (Equiv.Perm.sign (e₀.trans e₁.symm)).isUnit with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

omit [DecidableEq m] in
/-- If the rows of `A` sum to zero, then the column `a` is minus the sum of the other columns. -/
theorem sum_submatrix_ne_eq_neg (A : Matrix m n R) (hA : ∀ i, ∑ j, A i j = 0) {a : n}
    (e : m ≃ {j // j ≠ a}) (i : m) :
    ∑ k, A i (e k) = -A i a := by
  classical
  rw [eq_neg_iff_add_eq_zero, add_comm, ← hA i, Fintype.sum_eq_add_sum_subtype_ne (A i) a]
  congr 1
  exact e.sum_comp fun j : {j // j ≠ a} ↦ A i j

/-- If the rows of `A : Matrix m n R` sum to zero, then the `m × m` minors obtained by deleting
one column and identifying the remaining columns with `m` all have the same determinant up to
sign. -/
theorem det_submatrix_ne_eq_or_eq_neg (A : Matrix m n R) (hA : ∀ i, ∑ j, A i j = 0) {a b : n}
    (e₀ : m ≃ {j // j ≠ a}) (e₁ : m ≃ {j // j ≠ b}) :
    (A.submatrix id fun k ↦ (e₀ k : n)).det = (A.submatrix id fun k ↦ (e₁ k : n)).det ∨
      (A.submatrix id fun k ↦ (e₀ k : n)).det = -(A.submatrix id fun k ↦ (e₁ k : n)).det := by
  classical
  by_cases hab : a = b
  · subst hab
    exact det_submatrix_id_eq_or_eq_neg A Subtype.val e₀ e₁
  -- `f` exchanges the deleted columns `a` and `b`.
  let f : {j // j ≠ a} ≃ {j // j ≠ b} := (Equiv.swap a b).subtypeEquiv fun j ↦ by
    simp only [ne_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have hf : ∀ x : {j // j ≠ a}, (f x : n) = Equiv.swap a b x := fun x ↦ rfl
  set k₀ : m := e₀.symm ⟨b, Ne.symm hab⟩ with hk₀
  have hek₀ : (e₀ k₀ : n) = b := by simp [hk₀]
  set M₀ := A.submatrix id fun k ↦ (e₀ k : n) with hM₀
  -- Deleting `b` and reindexing through `e₀.trans f` replaces the column `b` of `M₀` by the
  -- column `a` of `A`.
  have h2 : (A.submatrix id fun k ↦ ((e₀.trans f) k : n)) = M₀.updateCol k₀ fun i ↦ A i a := by
    ext i k
    by_cases hk : k = k₀
    · subst hk
      simp [hf, hek₀]
    · rw [updateCol_ne hk]
      have hb : (e₀ k : n) ≠ b := fun h ↦ hk (e₀.injective (Subtype.ext (h.trans hek₀.symm)))
      simp [hM₀, hf, Equiv.swap_apply_of_ne_of_ne (e₀ k).2 hb]
  have h3 : ∀ i, A i a = -∑ k, M₀ i k := fun i ↦
    (neg_eq_iff_eq_neg.mpr (sum_submatrix_ne_eq_neg A hA e₀ i)).symm
  have h4 : (A.submatrix id fun k ↦ ((e₀.trans f) k : n)).det = -M₀.det := by
    rw [h2]
    have : (fun i ↦ A i a) = (-1 : R) • fun i ↦ ∑ k, (1 : R) • M₀ i k := by
      ext i
      simp [h3]
    rw [this, det_updateCol_smul, det_updateCol_sum]
    simp
  rcases det_submatrix_id_eq_or_eq_neg A Subtype.val (e₀.trans f) e₁ with h1 | h1
  · right
    rw [← h1, h4, neg_neg]
  · left
    rw [h4] at h1
    exact neg_inj.mp h1

variable {F : Type*} [Field F]

omit [DecidableEq m] in
/-- A matrix has full row rank exactly when its rows are linearly independent. -/
theorem rank_eq_card_iff_linearIndependent_row (A : Matrix m n F) :
    A.rank = Fintype.card m ↔ LinearIndependent F A.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← rank_eq_finrank_span_row, eq_comm]

/-- If the rows of `A : Matrix m n F` sum to zero, then the minor obtained by deleting one column
(and identifying the remaining columns with `m`) is nonsingular if and only if `A` has full row
rank. -/
theorem det_submatrix_ne_ne_zero_iff (A : Matrix m n F) (hA : ∀ i, ∑ j, A i j = 0) {a : n}
    (e : m ≃ {j // j ≠ a}) :
    (A.submatrix id fun k ↦ (e k : n)).det ≠ 0 ↔ A.rank = Fintype.card m := by
  classical
  constructor
  · intro h
    refine le_antisymm (rank_le_card_height A) ?_
    calc Fintype.card m
        = (A.submatrix id fun k ↦ (e k : n)).rank :=
          (rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h))).symm
      _ ≤ A.rank := rank_submatrix_le A id _
  · intro h
    have hli : LinearIndependent F A.row := (rank_eq_card_iff_linearIndependent_row A).1 h
    rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det, ← linearIndependent_rows_iff_isUnit,
      Fintype.linearIndependent_iff]
    intro g hg
    refine Fintype.linearIndependent_iff.1 hli g ?_
    have hg' : ∀ k, ∑ i, g i * A i (e k) = 0 := fun k ↦ by
      have := congrFun hg k
      simpa [Matrix.row, Finset.sum_apply] using this
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row]
    by_cases hj : j = a
    · subst hj
      have h3 : ∀ i, A i j = -∑ k, A i (e k) := fun i ↦ by
        rw [sum_submatrix_ne_eq_neg A hA e i, neg_neg]
      simp_rw [h3, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
      simp [hg']
    · simpa using hg' (e.symm ⟨j, hj⟩)

end Matrix
