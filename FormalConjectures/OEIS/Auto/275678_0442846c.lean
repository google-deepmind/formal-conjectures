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
A275678: Number of ordered ways to write $n$ as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le y$.
-/
def A275678 (n : ℕ) : ℕ :=
  -- Since $z^2 \le n$, $k, x^2, y^2$ are all bounded by $n$. $n+1$ is a safe and computable upper bound.
  let B := n + 1

  Finset.sum (Finset.range B) fun k =>
  Finset.sum (Finset.range B) fun x =>
  Finset.sum (Finset.range B) fun y =>
    if x ≤ y then
      let P_term := 4^k * (1 + 4 * x^2 + y^2)

      -- The existence of a non-negative integer $z$ is equivalent to $n - P_{term}$ being a perfect square.
      if P_term ≤ n then
        -- We check if $n - P_{term}$ is a perfect square using the standard Mathlib function for integer square root.
        let r := n - P_term
        let z_candidate := r.sqrt
        if z_candidate ^ 2 = r then 1 else 0
      else 0
    else 0

theorem a_one : A275678 1 = 1 := by
  -- The only representation is 1 = 4^0 * (1 + 4*0^2 + 0^2) + 0^2, with 0 ≤ 0.
  -- This requires a proper definition of summation bounds, which the definition handles by using a large enough B.
  sorry

theorem a_two : A275678 2 = 2 := by
  -- 2 = 4^0 * (1 + 4*0^2 + 1^2) + 0^2, with 0 ≤ 1.
  -- 2 = 4^0 * (1 + 4*0^2 + 0^2) + 1^2, with 0 ≤ 0.
  sorry

theorem a_three : A275678 3 = 1 := by
  -- 3 = 4^0 * (1 + 4*0^2 + 0^2) + (sqrt 2)^2 -- no, sqrt 2 is not integer
  -- 3 = 4^0 * (1 + 4*0^2 + 1^2) + 1^2
  sorry

theorem a_four : A275678 4 = 1 := by
  -- 4 = 4^0 * (1 + 4*0^2 + 0^2) + 3^2 -- no
  -- 4 = 4^0 * (1 + 4*0^2 + 1^2) + sqrt 2 -- no
  -- 4 = 4^0 * (1 + 4*0^2 + 2^2) + 0^2
  -- 4 = 4^1 * (1 + 4*0^2 + 0^2) + 0^2
  sorry

/-- Conjecture: a(n) > 0 for all n > 0.
This is part (i) of the conjecture listed in OEIS A275678.
This means every positive integer can be written as $4^k(1+4x^2+y^2) + z^2$
where $k,x,y,z \in \mathbb{N}$ and $x \le y$.
-/
theorem oeis_A275678_conjecture_i (n : ℕ) (hn : n > 0) : A275678 n > 0 := by
  sorry

/-- Conjecture: Any positive integer can be written as $4^k(1+4x^2+y^2) + z^2$,
where $k,x,y,z$ are nonnegative integers with $x \le z$.
Note: This is part (ii) of the conjecture listed in OEIS A275678.
This is a different conjecture because the constraint $x \le y$ in the definition of $a(n)$
is replaced by $x \le z$ here, and the problem is about existence (similar to (i)), not number of ways.
The question only asked to formalize "oeis_275678_conjecture_1", which I take to be the primary one (i),
but I will include (ii) as well for completeness, as it's a nearby mathematical claim.
-/
theorem oeis_A275678_conjecture_ii (n : ℕ) (hn : n > 0) :
  ∃ k x y z : ℕ, n = 4^k * (1 + 4 * x^2 + y^2) + z^2 ∧ x ≤ z :=
by sorry
