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
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Dittert conjecture

Let `Kₙ` be the set of nonnegative real `n × n` matrices whose entries sum to `n`.
For `A ∈ Kₙ`, define

`φ(A) = (∏ i, rowSum A i) + (∏ j, columnSum A j) - permanent A`.

The Dittert conjecture states that the matrix `Jₙ`, all of whose entries are `1 / n`,
is the unique maximizer of `φ` on `Kₙ`.

The conjecture is known for `n = 2`, `n = 3`, and `n = 4`.

*References:*
- [D. K. U. and K. Somasundaram, *Lih Wang and Dittert Conjectures on Permanents*]
  (https://arxiv.org/abs/2312.00464)
- [Formal Conjectures issue #2267]
  (https://github.com/google-deepmind/formal-conjectures/issues/2267)
-/

open scoped BigOperators

noncomputable section

namespace Arxiv.«2312.00464»

/-- The sum of all entries of a square real matrix. -/
def entrySum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j

/-- Membership in `Kₙ`: all entries are nonnegative and their total sum is `n`. -/
def MemKn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ entrySum A = n

/-- The sum of the entries in row `i`. -/
def rowSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, A i j

/-- The sum of the entries in column `j`. -/
def columnSum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  ∑ i, A i j

/-- Dittert's objective function. -/
def phi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∏ i, rowSum A i) + (∏ j, columnSum A j) - A.permanent

/-- The `n × n` matrix all of whose entries are `1 / n`. -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun _ _ ↦ 1 / n

/-- The one-dimensional uniform matrix satisfies the defining constraints of `K₁`. -/
@[category test, AMS 15]
theorem J_one_memKn : MemKn (J 1) := by
  simp [MemKn, entrySum, J]

/--
**Dittert conjecture.** For every positive `n`, `Jₙ` belongs to `Kₙ` and is the unique
maximizer of `φ` on `Kₙ`.
-/
@[category research open, AMS 5 15]
theorem dittert_conjecture (n : ℕ) (hn : 1 ≤ n) :
    MemKn (J n) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, MemKn A →
        phi A ≤ phi (J n) ∧ (phi A = phi (J n) ↔ A = J n) := by
  sorry

end Arxiv.«2312.00464»
