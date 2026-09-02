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
A275471: Number of ordered ways to write $n$ as $4^k(1+x^2+y^2)+z^2$, where $k,x,y,z$ are nonnegative integers with $x \le y$ and $x \equiv y \pmod 2$.
-/
def a (n : ℕ) : ℕ :=
  -- We count the number of solutions $(k, x, y, z)$ by summing over finite ranges of $k, x, y$,
  -- and checking if the remainder is a perfect square $z^2$.
  -- Bound for $k$ is loosely $n$. Bound for $x, y$ is $\lfloor\sqrt{n}\rfloor$.
  (Finset.range (n + 1)).sum fun k =>
    (Finset.range (n.sqrt + 1)).sum fun x =>
      (Finset.range (n.sqrt + 1)).sum fun y =>

        let term_inner := 1 + x^2 + y^2
        let term_outer := 4^k * term_inner

        -- 1. Constraints $x \le y$ and $x \equiv y \pmod 2$.
        -- 2. Constraint $4^k(1+x^2+y^2) \le n$ to ensure non-negative remainder $R$.
        if x ≤ y ∧ x % 2 = y % 2 ∧ term_outer ≤ n then
          let R : ℕ := n - term_outer
          -- 3. Constraint $R = z^2$, checked by $z^2 = R$ where $z = \lfloor\sqrt{R}\rfloor$.
          if R.sqrt * R.sqrt = R then 1 else 0
        else 0


theorem a_one : a 1 = 1 := by sorry
theorem a_two : a 2 = 1 := by sorry
theorem a_three : a 3 = 1 := by sorry
theorem a_four : a 4 = 2 := by sorry

/-- Conjecture: a(n) > 0 except for n = 449. -/
theorem oeis_a275471_conjecture : ∀ n : ℕ, n > 0 → (a n > 0 ↔ n ≠ 449) := by sorry
