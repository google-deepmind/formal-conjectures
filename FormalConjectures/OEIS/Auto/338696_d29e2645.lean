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

open Nat BigOperators Finset

/--
A338696: Number of ways to write $n$ as $x^3 + y^2 + z(3z+2)$, where $x$ and $y$ are nonnegative integers, and $z$ is an integer.
This count is equivalent to the number of pairs $(x, y) \in \mathbb{N}^2$ such that $x^3 + y^2 \le n$ and $3(n - x^3 - y^2) + 1$ is a perfect square.
-/
noncomputable def A338696 (n : ℕ) : ℕ :=
  -- We iterate up to $n+1$ for both $x$ and $y$, as the $x^3+y^2 \le n$ check handles the actual bounds.
  (range (n + 1)).sum fun x =>
    let x_cube := x ^ 3
    (range (n + 1)).sum fun y =>
      let y_sq := y ^ 2
      if x_cube + y_sq ≤ n then
        let k := n - (x_cube + y_sq)
        let m := 3 * k + 1
        -- Check if m is a perfect square: m = (sqrt m)^2
        if m.sqrt * m.sqrt = m then 1 else 0
      else 0

theorem a_one : A338696 1 = 3 := by
  -- Proof not required, but we keep the examples for context
  sorry

theorem a_two : A338696 2 = 3 := by
  sorry

theorem a_three : A338696 3 = 1 := by
  sorry

theorem a_four : A338696 4 = 1 := by
  sorry


/-- Conjecture: a(n) > 0 except for n = 19. -/
theorem oeis_338696_conjecture_0 (n : ℕ) : A338696 n > 0 ↔ n ≠ 19 := by
  sorry
