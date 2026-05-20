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
open Nat Finset

/--
A271714: Number of ordered ways to write $n$ as $w^2 + x^2 + y^2 + z^2$ such that $(10w+5x)^2 + (12y+36z)^2$ is a square, where $w$ is a positive integer and $x,y,z$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let S := range (n.sqrt + 1)
  S.sum fun w =>
  S.sum fun x =>
  S.sum fun y =>
  S.sum fun z =>
    -- The expression is 1 if all conditions hold, 0 otherwise.
    if w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ IsSquare ((10 * w + 5 * x)^2 + (12 * y + 36 * z)^2)
    then 1
    else 0

theorem a_one : a 1 = 1 := by
  -- Requires detailed Finset summation proof, left as is from prompt and assumed correct structure.
  sorry

theorem a_two : a 2 = 1 := by
  -- Requires detailed Finset summation proof, left as is from prompt and assumed correct structure.
  sorry

theorem a_three : a 3 = 1 := by
  -- Requires detailed Finset summation proof, left as is from prompt and assumed correct structure.
  sorry

theorem a_four : a 4 = 1 := by
  -- Requires detailed Finset summation proof, left as is from prompt and assumed correct structure.
  sorry

/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 7, 9, 19, 49, 133, 589, $2^k$, $2^k \cdot 3$, $4^k \cdot q$ ($k = 0,1,2,\dots$ and $q = 14, 67, 71, 199$).
-/
theorem oeis_271714_conjecture_0 (n : ℕ) :
  (n > 0 → a n > 0) ∧
  (a n = 1 ↔ n > 0 ∧ (
    n ∈ ({7, 9, 19, 49, 133, 589} : Set ℕ) ∨
    (∃ k : ℕ, n = 2^k) ∨ -- 2^k
    (∃ k : ℕ, n = 3 * 2^k) ∨ -- 2^k * 3
    (∃ k : ℕ, ∃ q : ℕ, q ∈ ({14, 67, 71, 199} : Set ℕ) ∧ n = 4^k * q) -- 4^k * q
  )) := by
  sorry
