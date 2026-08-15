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

import FormalConjectures.Util.ProblemImports

open Matrix Nat

/--
The $n \times n$ Catbert matrix $A_n$ with entries $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$,
where $C(k)$ is the $k$-th Catalan number (A000108).
-/
noncomputable def catbert_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => 1 / (catalan (i.val + j.val) : ℚ)

/--
A296056: Determinant of the inverse of the matrix $A_n$, where $A_n$ is the $n \times n$ matrix
defined by $A_n[i,j] = 1/C(i+j-2)$ for $1 \le i,j \le n$.
$$a(n) = \det(A_n^{-1}) = 1/\det(A_n)$$
-/
noncomputable def A296056 (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (catbert_matrix n).det⁻¹


theorem a_one : A296056 1 = 1 := by
  norm_num[ A296056]
  norm_num [catbert_matrix]

theorem a_two : A296056 2 = -2 := by
  norm_num [(A296056 ·)]
  norm_num [catbert_matrix, false,Matrix.det_fin_two]
  norm_num only[catalan_eq_centralBinom_div,Nat.centralBinom,Nat.choose]

theorem a_three : A296056 3 = -1400 := by
  delta A296056
  norm_num+decide[catbert_matrix,Matrix.det_fin_three]
  norm_num only[catalan_eq_centralBinom_div, true,id]
  norm_num only [Nat.centralBinom,Nat.choose]

theorem a_four : A296056 4 = -679140000 := by
  norm_num[ A296056]
  norm_num+decide[catbert_matrix,Matrix.det_succ_column_zero,inv_eq_iff_eq_inv,Fin.sum_univ_succ]
  norm_num+decide[catalan_eq_centralBinom_div, Fin.succAbove]
  norm_num only [Nat.centralBinom,Nat.choose]

/--
It is conjectured that a(n) is an integer for all n.
-/
theorem oeis_296056_conjecture_0 (n : ℕ) : A296056 n ∈ Set.range (Int.cast : ℤ → ℚ) :=
  by sorry
