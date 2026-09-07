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
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The matrix multiplication tensor

The matrix multiplication tensor has three modes indexing the entries of
$l \times m$, $m \times n$, and $n \times l$ matrices. Over a commutative ring,
its trilinear form is $(A,B,C) \mapsto \operatorname{tr}(ABC)$.

*Reference:* L. Chiantini, J. D. Hauenstein, C. Ikenmeyer, J. M. Landsberg, and G. Ottaviani,
[*Polynomials and the exponent of matrix multiplication*](https://doi.org/10.1112/blms.12147),
Bull. London Math. Soc. 50 (2018), 369–389, equation (1.1).
An accessible [preprint](https://arxiv.org/abs/1706.05074) is also available.
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
    apply Subtype.ext
    exact List.take_of_length_le (by simpa using t.property.length_eq.le)
  rw [← h]
  exact CPRankMax1.cons x _ (CPRankMax1.nil _)

private theorem cprank_le_of_cprankMax {ds : List ℕ} {x : Holor R ds} {r : ℕ}
    (h : CPRankMax r x) : cprank x ≤ r := by
  classical
  exact Nat.find_min' _ h

variable (R)

/-- The matrix multiplication tensor $\sum_{i,j,k} e_{ij} \otimes e_{jk} \otimes e_{ki}$.
The modes have sizes $lm$, $mn$, and $nl$. In a matrix with $m$ columns,
the coordinate $(i,j)$ is encoded by $i m + j$.
Over a commutative ring, its trilinear form is $(A,B,C) \mapsto \operatorname{tr}(ABC)$. -/
def matrixMulTensor (l m n : ℕ) : Holor R [l * m, m * n, n * l] :=
  ∑ i ∈ Finset.range l, ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range n,
    unitVec (l * m) (i * m + j) ⊗
      unitVec (m * n) (j * n + k) ⊗ unitVec (n * l) (k * l + i)

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

/-- The usual matrix multiplication algorithm gives a decomposition with $lmn$ summands. -/
theorem cprank_matrixMulTensor_le (l m n : ℕ) :
    (matrixMulTensor R l m n).cprank ≤ l * m * n := by
  apply cprank_le_of_cprankMax
  have h := cprankMax_sum (Finset.range l)
    (fun i ↦ ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range n,
      unitVec (l * m) (i * m + j) ⊗
        unitVec (m * n) (j * n + k) ⊗ unitVec (n * l) (k * l + i))
    (fun i _ ↦ cprankMax_sum (Finset.range m) _ (fun j _ ↦
      cprankMax_sum (Finset.range n) _ (fun k _ ↦
        cprankMax_1 (CPRankMax1.cons _ _
          (CPRankMax1.cons _ _ (cprankMax1_singleton (R := R) _))))))
  simpa [matrixMulTensor, Nat.mul_assoc] using h

@[simp]
theorem cprank_matrixMulTensor_zero : (matrixMulTensor R 0 0 0).cprank = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using cprank_matrixMulTensor_le R 0 0 0)

variable {R}

/-- Evaluate a three-mode holor on three coordinate vectors.
Over a commutative ring, this is trilinear in the vectors. -/
def trilinearEval {a b c : ℕ} (T : Holor R [a, b, c])
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) : R :=
  ∑ i : Fin a, ∑ j : Fin b, ∑ k : Fin c,
    T ⟨[i, j, k], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩ * x i * y j * z k

set_option backward.isDefEq.respectTransparency false in
theorem trilinearEval_sum {a b c : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Holor R [a, b, c])
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) :
    trilinearEval (∑ t ∈ s, T t) x y z = ∑ t ∈ s, trilinearEval (T t) x y z := by
  classical
  have hsum (p : HolorIndex [a, b, c]) : (∑ t ∈ s, T t) p = ∑ t ∈ s, T t p := by
    let ev : Holor R [a, b, c] →+ R :=
      { toFun := fun S ↦ S p
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    exact map_sum ev _ _
  simp only [trilinearEval]
  simp_rw [hsum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

theorem trilinearEval_unitVec {a b c : ℕ} (i : Fin a) (j : Fin b) (k : Fin c)
    (x : Fin a → R) (y : Fin b → R) (z : Fin c → R) :
    trilinearEval (unitVec a i ⊗ unitVec b j ⊗ unitVec c k) x y z = x i * y j * z k := by
  simp [trilinearEval, Holor.mul, HolorIndex.take, HolorIndex.drop, unitVec,
    Fin.val_eq_val]

/-- Evaluating the matrix multiplication tensor on the entries of $A$, $B$, and $C$
gives $\operatorname{tr}(ABC)$. The inverse of `finProdFinEquiv` decodes each
matrix coordinate into its row and column. -/
theorem trilinearEval_matrixMulTensor {l m n : ℕ}
    (A : Matrix (Fin l) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin l) R) :
    trilinearEval (matrixMulTensor R l m n)
      (fun p ↦ A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
      (fun p ↦ B (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
      (fun p ↦ C (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) =
      Matrix.trace (A * B * C) := by
  simp only [matrixMulTensor, Finset.sum_range]
  simp_rw [trilinearEval_sum]
  have hunit {a b : ℕ} (i : Fin a) (j : Fin b) :
      (unitVec (a * b) (i * b + j) : Holor R [a * b]) =
        unitVec (a * b) (finProdFinEquiv (i, j)) := by
    congr 1
    simp only [finProdFinEquiv_apply_val]
    ac_rfl
  simp_rw [hunit, trilinearEval_unitVec, Equiv.symm_apply_apply]
  simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

end Holor
