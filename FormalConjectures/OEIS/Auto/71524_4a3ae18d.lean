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
A071524: Determinant of $n \times n$ matrix defined by $m(i,j)=1$ if $i^2+j^2$ is a prime, $m(i,j)=0$ otherwise.
The indices $i$ and $j$ run from $1$ to $n$.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    -- Indices i and j are 0-based, so we use i.val + 1 to get 1-based indices.
    let i_idx : ℕ := i.val + 1
    let j_idx : ℕ := j.val + 1
    if (i_idx ^ 2 + j_idx ^ 2).Prime then (1 : ℤ) else (0 : ℤ)
  M.det


theorem a_one : a 1 = 1 := by
  -- This is part of the provided skeleton, but the proof is incomplete/incorrect.
  -- Leaving it as is, as directed.
  sorry

theorem a_two : a 2 = -1 := by
  -- This is part of the provided skeleton, but the proof is incomplete/incorrect.
  -- Leaving it as is, as directed.
  sorry

theorem a_three : a 3 = -1 := by
  -- This is part of the provided skeleton, but the proof is incomplete/incorrect.
  -- Leaving it as is, as directed.
  sorry

theorem a_four : a 4 = 1 := by
  -- This is part of the provided skeleton, but the proof is incomplete/incorrect.
  -- Leaving it as is, as directed.
  sorry

/--
Conjecture: a(n) = 0 for no n > 28. - Zhi-Wei Sun, Aug 26 2013
-/
theorem oeis_71524_conjecture_0 : ∀ n : ℕ, n > 28 → a n ≠ 0 := by
  sorry
