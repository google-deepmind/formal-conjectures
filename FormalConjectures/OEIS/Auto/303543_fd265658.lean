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
A303543: Number of ways to write $n$ as $a^2 + b^2 + C(k) + C(m)$ with $0 \le a \le b$ and $0 < k \le m$,
where $C(k)$ denotes the Catalan number $\binom{2k}{k}/(k+1)$.
-/
def A303543 (n : ℕ) : ℕ :=
  -- Helper function for the number of ways to write R as a^2 + b^2 with 0 ≤ a ≤ b.
  let count_sum_two_squares_ordered (R : ℕ) : ℕ :=
    -- Bounding a to sqrt(R/2) ensures a ≤ b if R-a^2 is a square b^2.
    let max_a := R / 2 |> Nat.sqrt
    (range (max_a + 1)).sum fun a =>
      let rem := R - a^2
      -- Check if rem is a perfect square.
      let b := rem.sqrt
      if b^2 = rem then 1 else 0

  -- Set a loose, safe upper bound for k and m.
  -- Since catalan numbers grow very fast, n is a much better bound than n+1,
  -- but the current definition uses n+1 which is mathematically correct since we only sum over k and m such that C_k + C_m <= n.
  let B := n + 1

  -- Sum over all combinations of k and m that satisfy 1 ≤ k ≤ m.
  (range B).sum fun k =>
    (range B).sum fun m =>
      if 1 ≤ k ∧ k ≤ m then
        let C_sum := catalan k + catalan m
        if C_sum ≤ n then
          count_sum_two_squares_ordered (n - C_sum)
        else
          0
      else
        0


theorem a_one : A303543 1 = 0 := by
  -- The proof block is left as is in the prompt, just for context, but not expanded.
  sorry

theorem a_two : A303543 2 = 1 := by
  sorry

theorem a_three : A303543 3 = 2 := by
  sorry

theorem a_four : A303543 4 = 3 := by
  sorry

/-- Conjecture: a(n) > 0 for all n > 1. In other words, any integer n > 1 can be written as the sum of two squares and two Catalan numbers. -/
theorem oeis_A303543_conjecture_1 : ∀ (n : ℕ), n > 1 → A303543 n > 0 := by
  sorry
