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

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.Discriminant

/-!
# The conjugate vectors of a basis of a number field

Let `K` be a number field and `E` an algebraically closed field of characteristic zero. Sending
`x : K` to the vector `fun σ : K →+* E ↦ σ x` of all its conjugates is an injective `ℚ`-linear
map `K → ((K →+* E) → E)` between spaces of the same dimension `[K : ℚ]`. We record the two
consequences used elsewhere:

## Main results

* `NumberField.linearIndependent_embeddings_of_basis`: the conjugate vectors of a `ℚ`-basis of
  `K` are linearly independent **over `E`**, not merely over `ℚ`. This is the statement that the
  matrix `(σ (b i))` is invertible, which follows from the discriminant of a basis being nonzero.
* `NumberField.exists_norm_repr_le`: when `E` is a complete normed field, the coordinates of `x`
  in a `ℚ`-basis are bounded by the sup norm of the vector of conjugates of `x`, uniformly in `x`.
  This is continuity of the coordinate functionals of a finite-dimensional normed `E`-space.
-/

@[expose] public section

namespace NumberField

open Module

variable {K : Type*} [Field K] [NumberField K]

section AlgClosed

variable {E : Type*} [Field E] [IsAlgClosed E] [CharZero E]

/-- The conjugate vectors `fun σ : K →+* E ↦ σ (b i)` of a `ℚ`-basis `b` of a number field `K`
are linearly independent over `E`.

The matrix `(σ (b i))_{i, σ}` is `Algebra.embeddingsMatrix`, whose determinant squares to the
discriminant of `b` (`Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two`), which is nonzero
(`Algebra.discr_not_zero_of_basis`). -/
theorem linearIndependent_embeddings_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ K) : LinearIndependent E fun i ↦ fun σ : K →+* E ↦ σ (b i) := by
  classical
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] E) := by
    rw [AlgHom.card ℚ K E, finrank_eq_card_basis b]
  set e : ι ≃ (K →ₐ[ℚ] E) := Fintype.equivOfCardEq hcard with he
  have hdet : (Algebra.embeddingsMatrixReindex ℚ E b e).det ≠ 0 := by
    intro h
    refine Algebra.discr_not_zero_of_basis ℚ b ?_
    have := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ E b e
    rw [h] at this
    simpa using (map_eq_zero_iff _ (algebraMap ℚ E).injective).1 (by simpa using this)
  have hrows : LinearIndependent E (Algebra.embeddingsMatrixReindex ℚ E b e).row :=
    Matrix.linearIndependent_rows_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  -- A relation among the conjugate vectors, read at the embeddings `e j`, is a relation among
  -- the rows of the (square) reindexed embeddings matrix.
  rw [Fintype.linearIndependent_iff]
  intro c hc
  refine Fintype.linearIndependent_iff.1 hrows c (funext fun j ↦ ?_)
  have hcj := congrFun hc (e j : K →+* E)
  simpa [Matrix.row, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
    Finset.sum_apply, smul_eq_mul] using hcj

end AlgClosed

section Normed

variable {E : Type*} [NontriviallyNormedField E] [CompleteSpace E] [IsAlgClosed E] [CharZero E]

/-- The coordinates of `x : K` in a `ℚ`-basis are bounded, uniformly in `x`, by the sup norm of
the vector `fun σ : K →+* E ↦ σ x` of the conjugates of `x`.

The conjugate vectors of the basis form a basis of `(K →+* E) → E` over `E`
(`linearIndependent_embeddings_of_basis` plus a dimension count), and the coordinate functionals
of a finite-dimensional normed space over a complete field are continuous, hence bounded. -/
theorem exists_norm_repr_le {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ K) :
    ∃ C : ℝ, ∀ (x : K) (i : ι),
      ‖algebraMap ℚ E (b.repr x i)‖ ≤ C * ‖fun σ : K →+* E ↦ σ x‖ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun _ i ↦ hι.elim i⟩
  have hcard : Fintype.card ι = finrank E ((K →+* E) → E) := by
    rw [finrank_fintype_fun_eq_card, Embeddings.card K E, finrank_eq_card_basis b]
  set B : Basis ι E ((K →+* E) → E) :=
    basisOfLinearIndependentOfCardEqFinrank (linearIndependent_embeddings_of_basis b) hcard
    with hB
  have hBapply : ∀ i, B i = fun σ : K →+* E ↦ σ (b i) := by
    intro i
    rw [hB, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- The coordinates of the conjugate vector of `x` are the conjugates of the coordinates of `x`.
  have hrepr : ∀ (x : K) (i : ι),
      B.repr (fun σ : K →+* E ↦ σ x) i = algebraMap ℚ E (b.repr x i) := by
    intro x i
    have hx : (fun σ : K →+* E ↦ σ x)
        = ∑ j, algebraMap ℚ E (b.repr x j) • B j := by
      funext σ
      conv_lhs => rw [← b.sum_repr x]
      rw [map_sum]
      simp only [Finset.sum_apply, Pi.smul_apply, hBapply, smul_eq_mul, Rat.smul_def, map_mul,
        map_ratCast, eq_ratCast]
    rw [hx]
    exact congrFun (B.repr_sum_self _) i
  refine ⟨∑ i, ‖LinearMap.toContinuousLinearMap (B.coord i)‖, fun x i ↦ ?_⟩
  have hle : ‖algebraMap ℚ E (b.repr x i)‖
      ≤ ‖LinearMap.toContinuousLinearMap (B.coord i)‖ * ‖fun σ : K →+* E ↦ σ x‖ := by
    rw [← hrepr x i, ← Basis.coord_apply]
    exact (LinearMap.toContinuousLinearMap (B.coord i)).le_opNorm _
  refine hle.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Finset.single_le_sum
    (f := fun j ↦ ‖LinearMap.toContinuousLinearMap (B.coord j)‖)
    (fun j _ ↦ norm_nonneg _) (Finset.mem_univ i)

end Normed

end NumberField
