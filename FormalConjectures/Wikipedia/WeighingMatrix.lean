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

/-!
# Weighing matrices and the Geramita–Seberry conjecture

A *weighing matrix* $W(n, w)$ of order $n$ and weight $w$ is an $n \times n$ matrix with entries in
$\{-1, 0, 1\}$ satisfying $W W^{\mathsf{T}} = w I_n$. At $w = n$, this recovers Hadamard matrices.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Weighing_matrix)
- [GS79] Geramita, A. V. and Seberry, J. (1979). *Orthogonal Designs: Quadratic Forms and Hadamard
  Matrices*, Lecture Notes in Pure and Applied Mathematics 45, Marcel Dekker, New York.
-/

@[expose] public section

namespace WeighingMatrix

/-- `W` is a **weighing matrix** $W(n, w)$ of order $n$ and weight $w$ if its entries lie in
$\{-1, 0, 1\}$ and $W W^{\mathsf{T}} = w I_n$. -/
def IsWeighingMatrix (n w : ℕ) (W : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1) ∧
    W * W.transpose = (w : ℤ) • 1

/-- For every order $n$, the zero matrix is a weighing matrix $W(n, 0)$ of weight $0$. -/
@[category API, AMS 5 15]
theorem isWeighingMatrix_zero (n : ℕ) : IsWeighingMatrix n 0 0 :=
  ⟨fun _ _ => .inr (.inl rfl), by simp⟩

/-- For every order $n$, the identity matrix is a weighing matrix $W(n, 1)$ of weight $1$. -/
@[category API, AMS 5 15]
theorem isWeighingMatrix_one (n : ℕ) : IsWeighingMatrix n 1 1 := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- Negating a weighing matrix $W(n, w)$ yields a weighing matrix of the same order and weight. -/
@[category API, AMS 5 15]
theorem IsWeighingMatrix.neg {n w : ℕ} {W : Matrix (Fin n) (Fin n) ℤ}
    (hW : IsWeighingMatrix n w W) :
    IsWeighingMatrix n w (-W) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rcases hW.1 i j with h | h | h <;> simp [h]
  · rw [Matrix.transpose_neg, neg_mul_neg, hW.2]

/-- The $2 \times 2$ Sylvester matrix $\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ is a weighing
matrix $W(2, 2)$. -/
@[category test, AMS 5 15]
theorem isWeighingMatrix_two_two : IsWeighingMatrix 2 2 !![1, 1; 1, -1] := by
  refine ⟨fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- No weighing matrix $W(2, 3)$ exists because each row of length $2$ over $\{-1, 0, 1\}$ has
squared norm at most $2$. -/
@[category test, AMS 5 15]
theorem not_exists_isWeighingMatrix_two_three : ¬ ∃ W, IsWeighingMatrix 2 3 W := by
  rintro ⟨W, hent, hmul⟩
  have h00 := congrArg (fun M => M 0 0) hmul
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hsq0 : W 0 0 * W 0 0 ≤ 1 := by
    rcases hent 0 0 with h | h | h <;> rw [h] <;> norm_num
  have hsq1 : W 0 1 * W 0 1 ≤ 1 := by
    rcases hent 0 1 with h | h | h <;> rw [h] <;> norm_num
  linarith

/--
**Weighing matrix conjecture** (Wallis 1972; Geramita–Seberry [GS79]): for every positive integer
$m \ge 1$ and every weight $0 \le w \le 4m$, there exists a weighing matrix $W(4m, w)$ of order
$4m$ and weight $w$.

At $w = 4m$, this specializes to Hadamard's conjecture.
-/
@[category research open, AMS 5 15]
theorem weighing_matrix_conjecture (m w : ℕ) (hm : 1 ≤ m) (hw : w ≤ 4 * m) :
    ∃ W, IsWeighingMatrix (4 * m) w W := by
  sorry

/--
**Asymptotic existence of weighing matrices** (Geramita–Seberry [GS79]): for every fixed weight
$w$, a weighing matrix $W(4m, w)$ exists for all sufficiently large multiples $4m$.
-/
@[category research solved, AMS 5 15]
theorem weighing_matrix_conjecture.variants.asymptotic (w : ℕ) :
    ∀ᶠ m in Filter.atTop, ∃ W, IsWeighingMatrix (4 * m) w W := by
  sorry

end WeighingMatrix
