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
The number of ways to write $k$ as $a^2 + b^2$, where $a, b \in \mathbb{ℕ}$ with $a \le b$.
This is found by iterating over $a$ such that $2a^2 \le k$ (which means $a \le \lfloor \sqrt{k/2} \rfloor$)
and checking if $k - a^2$ is a perfect square $b^2$.
-/
def num_sum_sq_le (k : ℕ) : ℕ :=
  (Finset.range (Nat.sqrt (k / 2) + 1)).sum fun a =>
    let r := k - a ^ 2
    if r.sqrt * r.sqrt = r then 1 else 0

/--
A303656: Number of ways to write $n$ as $a^2 + b^2 + 3^c + 5^d$, where $a,b,c,d$ are nonnegative
integers with $a \le b$.
-/
def A303656 (n : ℕ) : ℕ :=
  if n = 0 then 0 else

  let C_max := Nat.log 3 n
  let D_max := Nat.log 5 n

  (range (C_max + 1)).sum fun c =>
    (range (D_max + 1)).sum fun d =>
      let sum_powers  := 3 ^ c + 5 ^ d

      if sum_powers ≤ n then
        num_sum_sq_le (n - sum_powers)
      else
        0


theorem a_one : A303656 1 = 0 := by
  sorry

theorem a_two : A303656 2 = 1 := by
  sorry

theorem a_three : A303656 3 = 1 := by
  sorry

theorem a_four : A303656 4 = 2 := by
  sorry

/--
Conjecture (Zhi-Wei Sun): a(n) > 0 for all n > 1. In other words, any integer n > 1
can be written as the sum of two squares, a power of 3 and a power of 5.
-/
theorem oeis_303656_conjecture_0 : ∀ n : ℕ, n > 1 → A303656 n > 0 := by
  sorry
