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

import FormalConjecturesUtil

/-!
# Dittert conjecture

*Reference:*
- [D. K. U. and K. Somasundaram, *Lih Wang and Dittert Conjectures on Permanents*]
  (https://arxiv.org/abs/2312.00464)
-/

open scoped BigOperators

noncomputable section

namespace Arxiv.«2312.00464»

/-- The sum of all entries of a square real matrix. -/
def entrySum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j

/-- Membership in $K_n$: all entries are nonnegative and their total sum is $n$. -/
def MemKn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ entrySum A = n

/-- The sum of the entries in row $i$. -/
def rowSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, A i j

/-- The sum of the entries in column $j$. -/
def columnSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ i, A i j

/-- Dittert's objective function. -/
def phi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∏ i, rowSum A i) + (∏ j, columnSum A j) - A.permanent

/-- The $n \times n$ matrix all of whose entries are $1 / n$. -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ ↦ 1 / n

/-- The one-dimensional uniform matrix satisfies the defining constraints of $K_1$. -/
@[category test, AMS 15]
theorem J_one_memKn : MemKn (J 1) := by
  simp [MemKn, entrySum, J]

/-- The row and column sums of the one-dimensional uniform matrix are both one. -/
@[category test, AMS 15]
theorem J_one_rowSum_and_columnSum (i j : Fin 1) :
    rowSum (J 1) i = 1 ∧ columnSum (J 1) j = 1 := by
  simp [rowSum, columnSum, J]

/-- Dittert's objective evaluates to one on the one-dimensional uniform matrix. -/
@[category test, AMS 15]
theorem phi_J_one : phi (J 1) = 1 := by
  simp [phi, rowSum, columnSum, J, Matrix.permanent]

/--
**Dittert conjecture.** For every positive $n$, $J_n$ belongs to $K_n$ and is the unique
maximizer of $\varphi$ on $K_n$. The conjecture is known for $n = 2$, $n = 3$, and $n = 4$.
-/
@[category research open, AMS 5 15]
theorem dittert_conjecture (n : ℕ) (hn : 1 ≤ n) :
    MemKn (J n) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, MemKn A →
        phi A ≤ phi (J n) ∧ (phi A = phi (J n) ↔ A = J n) := by
  sorry

end Arxiv.«2312.00464»
