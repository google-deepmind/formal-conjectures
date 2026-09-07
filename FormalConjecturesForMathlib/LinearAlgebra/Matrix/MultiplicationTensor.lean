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

/-!
# The matrix multiplication tensor

The matrix multiplication tensor has three modes, each indexing the entries of an
$n \times n$ matrix. Over a commutative ring, its trilinear form is
$(A,B,C) \mapsto \operatorname{tr}(ABC)$.

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
Each matrix coordinate $(i,j)$ is encoded by $i n + j$ in a mode of size $n^2$.
Over a commutative ring, its trilinear form is $(A,B,C) \mapsto \operatorname{tr}(ABC)$. -/
def matrixMulTensor (n : ℕ) : Holor R [n * n, n * n, n * n] :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
    unitVec (n * n) (i * n + j) ⊗
      unitVec (n * n) (j * n + k) ⊗ unitVec (n * n) (k * n + i)

@[simp]
theorem matrixMulTensor_zero : matrixMulTensor R 0 = 0 := by
  simp [matrixMulTensor]

@[simp]
theorem matrixMulTensor_one :
    matrixMulTensor R 1 = unitVec 1 0 ⊗ unitVec 1 0 ⊗ unitVec 1 0 := by
  simp [matrixMulTensor]

/-- The usual matrix multiplication algorithm gives a decomposition with $n^3$ summands. -/
theorem cprank_matrixMulTensor_le (n : ℕ) : cprank (matrixMulTensor R n) ≤ n ^ 3 := by
  apply cprank_le_of_cprankMax
  have h := cprankMax_sum (Finset.range n)
    (fun i ↦ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      unitVec (n * n) (i * n + j) ⊗
        unitVec (n * n) (j * n + k) ⊗ unitVec (n * n) (k * n + i))
    (fun i _ ↦ cprankMax_sum (Finset.range n) _ (fun j _ ↦
      cprankMax_sum (Finset.range n) _ (fun k _ ↦
        cprankMax_1 (CPRankMax1.cons _ _
          (CPRankMax1.cons _ _ (cprankMax1_singleton (R := R) _))))))
  simpa [matrixMulTensor, Nat.pow_succ, Nat.mul_assoc] using h

@[simp]
theorem cprank_matrixMulTensor_zero : cprank (matrixMulTensor R 0) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using cprank_matrixMulTensor_le R 0)

end Holor
