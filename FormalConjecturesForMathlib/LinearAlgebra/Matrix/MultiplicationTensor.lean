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

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import FormalConjecturesForMathlib.LinearAlgebra.PiTensorProduct.Rank

/-!
# The matrix multiplication tensor

For finite types `m`, `n`, `p`, the matrix multiplication tensor
$\langle m, n, p\rangle = \sum_{i, j, k} e_{ij} \otimes e_{jk} \otimes e_{ki}$ is an element of
the tensor product of `Matrix m n R`, `Matrix n p R` and `Matrix p m R`. Pairing it with matrices
`A`, `B`, `C` in the three modes gives $\operatorname{tr}(ABC)$, and its tensor rank is the number
of multiplications needed to multiply an `m × n` matrix by an `n × p` matrix bilinearly.

*Reference:* L. Chiantini et al.,
[*Polynomials and the exponent of matrix multiplication*](https://doi.org/10.1112/blms.12147),
Bull. London Math. Soc. 50 (2018), 369–389, equation (1.1)
([preprint](https://arxiv.org/abs/1706.05074)).
-/

@[expose] public section

open PiTensorProduct
open scoped TensorProduct

universe u v

namespace Matrix

variable (R : Type u) [CommSemiring R] (m n p : Type v)

/-- The three mode spaces `Matrix m n R`, `Matrix n p R` and `Matrix p m R` of the matrix
multiplication tensor. -/
abbrev MulTensorSpace : Fin 3 → Type (max u v)
  | ⟨0, _⟩ => Matrix m n R
  | ⟨1, _⟩ => Matrix n p R
  | ⟨2, _⟩ => Matrix p m R

instance addCommMonoidMulTensorSpace (i : Fin 3) : AddCommMonoid (MulTensorSpace R m n p i) :=
  match i with
  | ⟨0, _⟩ => inferInstanceAs (AddCommMonoid (Matrix m n R))
  | ⟨1, _⟩ => inferInstanceAs (AddCommMonoid (Matrix n p R))
  | ⟨2, _⟩ => inferInstanceAs (AddCommMonoid (Matrix p m R))

instance moduleMulTensorSpace (i : Fin 3) : Module R (MulTensorSpace R m n p i) :=
  match i with
  | ⟨0, _⟩ => inferInstanceAs (Module R (Matrix m n R))
  | ⟨1, _⟩ => inferInstanceAs (Module R (Matrix n p R))
  | ⟨2, _⟩ => inferInstanceAs (Module R (Matrix p m R))

section FrobeniusPairing

variable {R m n} [Fintype m] [Fintype n]

/-- The Frobenius pairing `X ↦ ∑ i j, A i j * X i j` with a fixed matrix `A`, as a linear map. -/
def frobeniusPairing (A : Matrix m n R) : Matrix m n R →ₗ[R] R where
  toFun X := ∑ i, ∑ j, A i j * X i j
  map_add' X Y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.mul_sum, mul_left_comm]

@[simp]
theorem frobeniusPairing_apply (A X : Matrix m n R) :
    frobeniusPairing A X = ∑ i, ∑ j, A i j * X i j :=
  rfl

theorem frobeniusPairing_single [DecidableEq m] [DecidableEq n] (A : Matrix m n R) (i : m)
    (j : n) : frobeniusPairing A (single i j 1) = A i j := by
  rw [frobeniusPairing_apply, Fintype.sum_eq_single i, Fintype.sum_eq_single j]
  · simp
  all_goals
    intro b hb
    simp [hb.symm]

end FrobeniusPairing

section MulTensorTerm

variable {m n p} [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The three matrices `single i j 1`, `single j k 1`, `single k i 1` making up the `(i, j, k)`
term of the matrix multiplication tensor. -/
def mulTensorTerm (i : m) (j : n) (k : p) : ∀ s, MulTensorSpace R m n p s
  | ⟨0, _⟩ => single i j 1
  | ⟨1, _⟩ => single j k 1
  | ⟨2, _⟩ => single k i 1

@[simp]
theorem mulTensorTerm_zero (i : m) (j : n) (k : p) : mulTensorTerm R i j k 0 = single i j 1 := rfl

@[simp]
theorem mulTensorTerm_one (i : m) (j : n) (k : p) : mulTensorTerm R i j k 1 = single j k 1 := rfl

@[simp]
theorem mulTensorTerm_two (i : m) (j : n) (k : p) : mulTensorTerm R i j k 2 = single k i 1 := rfl

end MulTensorTerm

section MulTensor

variable [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- The matrix multiplication tensor
$\langle m, n, p\rangle = \sum_{i, j, k} e_{ij} \otimes e_{jk} \otimes e_{ki}$. -/
noncomputable def mulTensor : ⨂[R] s, MulTensorSpace R m n p s :=
  ∑ i, ∑ j, ∑ k, tprod R (mulTensorTerm R i j k)

@[simp]
theorem mulTensor_of_isEmpty_left [IsEmpty m] : mulTensor R m n p = 0 := by
  simp [mulTensor]

@[simp]
theorem mulTensor_of_isEmpty_middle [IsEmpty n] : mulTensor R m n p = 0 := by
  simp [mulTensor]

@[simp]
theorem mulTensor_of_isEmpty_right [IsEmpty p] : mulTensor R m n p = 0 := by
  simp [mulTensor]

theorem mulTensor_of_unique [Unique m] [Unique n] [Unique p] :
    mulTensor R m n p = tprod R (mulTensorTerm R default default default) := by
  simp [mulTensor]

/-- The standard algorithm gives a decomposition with `|m| * |n| * |p|` summands. -/
theorem tensorRank_mulTensor_le :
    (mulTensor R m n p).tensorRank ≤ Fintype.card m * Fintype.card n * Fintype.card p := by
  have h := tensorRank_sum_tprod_le (R := R)
    fun t : m × n × p ↦ mulTensorTerm R t.1 t.2.1 t.2.2
  simpa [mulTensor, Fintype.sum_prod_type, Fintype.card_prod, mul_assoc] using h

variable {R m n p}

/-- The multilinear map `(X, Y, Z) ↦ ⟪A, X⟫ * ⟪B, Y⟫ * ⟪C, Z⟫` pairing the three modes of the
matrix multiplication tensor with the matrices `A`, `B`, `C` via the Frobenius pairing. -/
def mulTensorPairing (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p m R) :
    MultilinearMap R (MulTensorSpace R m n p) R :=
  (MultilinearMap.mkPiAlgebra R (Fin 3) R).compLinearMap fun s ↦
    match s with
    | ⟨0, _⟩ => frobeniusPairing A
    | ⟨1, _⟩ => frobeniusPairing B
    | ⟨2, _⟩ => frobeniusPairing C

@[simp]
theorem mulTensorPairing_mulTensorTerm (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p m R)
    (i : m) (j : n) (k : p) :
    mulTensorPairing A B C (mulTensorTerm R i j k) = A i j * B j k * C k i := by
  simp only [mulTensorPairing, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_three, mulTensorTerm_zero, mulTensorTerm_one,
    mulTensorTerm_two, frobeniusPairing_single]

/-- Pairing the matrix multiplication tensor with matrices `A`, `B`, `C` gives
$\operatorname{tr}(ABC)$. -/
theorem lift_mulTensorPairing_mulTensor (A : Matrix m n R) (B : Matrix n p R)
    (C : Matrix p m R) :
    lift (mulTensorPairing A B C) (mulTensor R m n p) = (A * B * C).trace := by
  simp only [mulTensor, map_sum, lift.tprod, mulTensorPairing_mulTensorTerm, trace, diag,
    mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

end MulTensor

end Matrix
