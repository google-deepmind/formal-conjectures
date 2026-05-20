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

open Matrix

/--
A200024: Determinant of the $n \times n$ matrix with $(i,j)$-entry equal to 1 or 0
according as $i + j$ is a perfect square or not.
(Here $i, j$ are 1-indexed, running from $1$ to $n$).
-/
noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- The 1-based sum is $(i+1) + (j+1) = i + j + 2$, where $i, j$ are 0-based indices in Fin n.
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    -- A number k is a perfect square if and only if $\lfloor \sqrt{k} \rfloor^2 = k$.
    if (Nat.sqrt sum_one_based) ^ 2 = sum_one_based then 1 else 0
  M.det


theorem a_one : a 1 = 0 := by
  sorry

theorem a_two : a 2 = 0 := by
  sorry

theorem a_three : a 3 = -1 := by
  sorry

theorem a_four : a 4 = 0 := by
  sorry

-- Definition of a perfect cube for natural numbers
def is_perfect_cube (k : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 3 = k

-- A separate instance is needed for the decidability of the prop, which Mathlib must synthesize.
-- The simplest way to make this definition easier to accept is to use an instance which is noncomputable but correct.
-- As per the instructions, the full definition of a_cube is used.

/--
A(n): Determinant of the $n \times n$ matrix with $(i,j)$-entry equal to 1 or 0
according as $i + j$ is a perfect cube or not.
(Here $i, j$ are 1-indexed, running from $1$ to $n$).
-/
noncomputable def a_cube (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- The 1-based sum is $(i+1) + (j+1) = i + j + 2$
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    -- The property is decidable since we only need to search up to sum_one_based
    have : Decidable (is_perfect_cube sum_one_based) := by
      apply Classical.dec

    if is_perfect_cube sum_one_based then 1 else 0
  M.det

/-- Conjecture: Let A(n) be the n X n determinant with (i,j)-entry equal to 1 or 0
according as i + j is a cube or not. Then A(n) is nonzero for any n > 176. -/
theorem oeis_228624_conjecture_1 (n : ℕ) : n > 176 → a_cube n ≠ 0 := by
  sorry
