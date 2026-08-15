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
The $x$-th pentagonal number, $\frac{x(3x-1)}{2}$, for $x \ge 0$.
-/
private def pentagonal_first (x : ℕ) : ℕ := (x * (3 * x - 1)) / 2

/--
The $y$-th "second pentagonal number", $\frac{y(3y+1)}{2}$, for $y \ge 0$.
-/
private def pentagonal_second (y : ℕ) : ℕ := (y * (3 * y + 1)) / 2

/--
The number of $\mathbb{Z}$ indices $m$ such that $m(4m-3)=r$. This is 1 if $r$ is a
generalized decagonal number (i.e., $16r+9$ is a perfect square), and 0 otherwise.
-/
private def count_generalized_decagonal_index (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/--
A253187: Number of ordered ways to write $n$ as the sum of a pentagonal number, a second pentagonal number and a generalized decagonal number.
$$a(n) = \# \{ (x, y, m) \in \mathbb{N} \times \mathbb{N} \times \mathbb{Z} \mid n = \frac{x(3x-1)}{2} + \frac{y(3y+1)}{2} + m(4m-3) \}$$
-/
def A253187 (n : ℕ) : ℕ :=
  -- Iterate x and y up to n, which is a sufficient bound.
  (range (n + 1)).sum fun x =>
    (range (n + 1)).sum fun y =>
      let sum_pent := pentagonal_first x + pentagonal_second y
      if sum_pent <= n then
        count_generalized_decagonal_index (n - sum_pent)
      else
        0


theorem a_zero : A253187 0 = 1 := by
  sorry

theorem a_one : A253187 1 = 2 := by
  sorry

theorem a_two : A253187 2 = 2 := by
  sorry

theorem a_three : A253187 3 = 2 := by
  sorry

/-- Conjecture: a(n) > 0 for all n.
See also the author's similar conjectures in A254574, A254631, A255916 and the two linked papers. -/
theorem oeis_253187_conjecture_1 : ∀ (n : ℕ), A253187 n > 0 := by
  sorry
