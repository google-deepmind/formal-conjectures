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
open Nat

/--
A356026: Main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
Let $A(i, j)$ be the $(i, j)$-th term of the array, for $i, j \ge 1$.
$$A(i, j) = \begin{cases} i + j - 1 & \text{if } j \ge 2i - 3 \\ A(i - 1, i + (j - 2)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is even} \\ A(i - 1, i - (j + 3)/2) & \text{if } j < 2i - 3 \text{ and } j \text{ is odd} \end{cases}$$
The sequence $a(n)$ is $A(n, n)$.
-/
def KL_array : ℕ → ℕ → ℕ
| 0, _ => 0  -- Error case for 0 index
| _, 0 => 0  -- Error case for 0 index
| i, j =>
  if j ≥ 2 * i - 3 then
    i + j - 1
  else
    let i' := i - 1
    if j % 2 = 0 then
      let next_j := i + (j - 2) / 2
      KL_array i' next_j
    else
      let term := (j + 3) / 2
      let next_j := i - term
      KL_array i' next_j
termination_by i j => i

/--
The main diagonal of right-and-left variant of Kimberling expulsion array, A007063.
-/
def a (n : ℕ) : ℕ := KL_array n n


theorem a_one : a 1 = 1 := by sorry

theorem a_two : a 2 = 3 := by sorry

theorem a_three : a 3 = 5 := by sorry

theorem a_four : a 4 = 7 := by sorry


/--
A356026 Conjectures involving a = A007063 and b = A356026:
(1) Every positive integer is eventually expelled in b (A356026).
This means that the sequence $b(n) = A356026(n)$ is surjective onto the positive integers,
i.e., every positive natural number appears in the sequence $a(n)$ for some $n \ge 1$.
-/
theorem oeis_a356026_conjecture_1_part_b : ∀ k : ℕ, 0 < k → ∃ n : ℕ, 0 < n ∧ a n = k :=
by sorry
