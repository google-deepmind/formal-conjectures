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

public import Mathlib.Data.Holor
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The matrix multiplication tensor

*Reference:* L. Chiantini et al.,
[*Polynomials and the exponent of matrix multiplication*](https://doi.org/10.1112/blms.12147),
Bull. London Math. Soc. 50 (2018), 369–389, equation (1.1)
([preprint](https://arxiv.org/abs/1706.05074)).
-/

@[expose] public section

namespace Holor

variable {R : Type} [Ring R]

local infixr:70 " ⊗ " => Holor.mul

private theorem cprankMax1_singleton {d : ℕ} (x : Holor R [d]) : CPRankMax1 x := by
  have h : x ⊗ (fun _ ↦ (1 : R) : Holor R []) = x := by
    funext t
    simp only [Holor.mul, mul_one]
    congr 1
    exact Subtype.ext (List.take_of_length_le (by simpa using t.property.length_eq.le))
  rw [← h]
  exact .cons x _ (.nil _)

@[simp]
theorem cprank_zero {ds : List ℕ} : (0 : Holor R ds).cprank = 0 := by
  classical
  exact Nat.le_zero.mp (Nat.find_min' _ CPRankMax.zero)

variable (R)

/-- The tensor $\sum_{i,j,k} e_{ij} \otimes e_{jk} \otimes e_{ki}$ for
$l \times m$, $m \times n$, and $n \times l$ matrices, with row-major coordinates. -/
def matrixMulTensor (l m n : ℕ) : Holor R [l * m, m * n, n * l] :=
  ∑ i : Fin l, ∑ j : Fin m, ∑ k : Fin n,
    unitVec (l * m) (finProdFinEquiv (i, j)) ⊗
      unitVec (m * n) (finProdFinEquiv (j, k)) ⊗ unitVec (n * l) (finProdFinEquiv (k, i))

@[simp]
theorem matrixMulTensor_zero_left (m n : ℕ) : matrixMulTensor R 0 m n = 0 := by
  simp [matrixMulTensor]

@[simp]
theorem matrixMulTensor_zero_middle (l n : ℕ) : matrixMulTensor R l 0 n = 0 := by
  simp [matrixMulTensor]

@[simp]
theorem matrixMulTensor_zero_right (l m : ℕ) : matrixMulTensor R l m 0 = 0 := by
  simp [matrixMulTensor]

@[simp]
theorem matrixMulTensor_one :
    matrixMulTensor R 1 1 1 = unitVec 1 0 ⊗ unitVec 1 0 ⊗ unitVec 1 0 := by
  simp [matrixMulTensor]

/-- The standard decomposition has $lmn$ summands. -/
theorem cprank_matrixMulTensor_le (l m n : ℕ) :
    (matrixMulTensor R l m n).cprank ≤ l * m * n := by
  classical
  apply Nat.find_min'
  unfold matrixMulTensor
  simp_rw [← Fintype.sum_prod_type']
  convert! cprankMax_sum (n := 1) Finset.univ _ ?_ using 1
  · simp [Nat.mul_assoc]
  intro p _
  exact cprankMax_1 (.cons _ _ (.cons _ _ (cprankMax1_singleton _)))

variable {R}

/-- Evaluate a three-mode holor on vectors; trilinear over a commutative ring. -/
def trilinearEval {a b c : ℕ} (T : Holor R [a, b, c])
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) : R :=
  ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
    T ⟨[i, j, k], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ * x i * y j * z k

theorem trilinearEval_sum {a b c : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Holor R [a, b, c])
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) :
    trilinearEval (∑ t ∈ s, T t) x y z = ∑ t ∈ s, trilinearEval (T t) x y z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change trilinearEval (fun _ ↦ 0) x y z = 0
    simp [trilinearEval]
  | @insert t s ht ih =>
    simp only [Finset.sum_insert ht]
    rw [← ih]
    change trilinearEval (fun p ↦ T t p + (∑ u ∈ s, T u) p) x y z = _
    simp [trilinearEval, add_mul, Finset.sum_add_distrib]

theorem trilinearEval_unitVec {a b c : ℕ} (i : Fin a) (j : Fin b) (k : Fin c)
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) :
    trilinearEval (unitVec a i ⊗ unitVec b j ⊗ unitVec c k) x y z = x i * y j * z k := by
  simp [trilinearEval, Holor.mul, HolorIndex.take, HolorIndex.drop, unitVec,
    Fin.val_eq_val]

/-- The matrix multiplication tensor evaluates to $\operatorname{tr}(ABC)$. -/
theorem trilinearEval_matrixMulTensor {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin l) R) :
    trilinearEval (matrixMulTensor R l m n)
      (Function.uncurry A ∘ finProdFinEquiv.symm)
      (Function.uncurry B ∘ finProdFinEquiv.symm)
      (Function.uncurry C ∘ finProdFinEquiv.symm) =
      (A * B * C).trace := by
  dsimp only [Function.comp_def, Function.uncurry]
  simp only [matrixMulTensor]
  simp_rw [trilinearEval_sum, trilinearEval_unitVec, Equiv.symm_apply_apply]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_comm)

end Holor
