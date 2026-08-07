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
A helper function for counting the number of ways to write $k$ as $z^2 + w^2$ with $z, w \ge 0$ and $z \le w$.
-/
def count_restricted_two_squares (k : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ^ 2 + p.2 ^ 2 = k ∧ p.1 ≤ p.2)
    (Finset.product (Finset.range (sqrt k + 1)) (Finset.range (sqrt k + 1)))
  )

/--
A300667: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$
such that $3*x$ or $y$ is a square and $x + 2*y$ is also a square.
-/
def a (n : ℕ) : ℕ :=
  -- Define the "is a square" predicate based on its property with the integer square root.
  let is_sq (m : ℕ) : Prop := (sqrt m) * (sqrt m) = m

  Finset.sum (Finset.range (sqrt n + 1)) fun x =>
    let n_minus_x2 := n - x^2
    Finset.sum (Finset.range (sqrt n_minus_x2 + 1)) fun y =>
      -- Check conditions on x and y
      if is_sq (x + 2 * y) ∧ (is_sq (3 * x) ∨ is_sq y) then
        let k := n_minus_x2 - y^2
        count_restricted_two_squares k
      else 0


theorem a_zero : a 0 = 1 := by
  sorry

theorem a_one : a 1 = 2 := by
  sorry

theorem a_two : a 2 = 2 := by
  sorry

theorem a_three : a 3 = 1 := by
  sorry

/--
Conjecture 1 (positivity part): a(n) > 0 for all n >= 0.

The full text of the OEIS comment block which includes this conjecture is:
A300667 a(n) > 0 for all n = 0..10^8. Also, Conjecture 2 holds for all n = 0..10^8. In a 2018 paper Y.-C. Sun and Z.-W. Sun proved that any nonnegative integer can be written as x^2 + y^2 + z^2 + w^2 with x + 2*y a square, where x,y,z,w are nonnegative integers. - _Zhi-Wei Sun_, Oct 04 2020
-/
theorem oeis_a300667_conjecture_1_positivity (n : ℕ) : a n > 0 := by
  sorry
