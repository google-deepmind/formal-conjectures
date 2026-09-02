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
$p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number.
-/
def pentagonal (y : ℕ) : ℕ := (3 * y ^ 2 - y) / 2

/--
$p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number.
-/
def hexagonal (z : ℕ) : ℕ := 2 * z ^ 2 - z

/--
A160324: Number of ways to express $n$ as the sum of a square, a pentagonal number and a hexagonal number.
$$a(n) = \left| \left\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n \right\} \right|$$
-/
def a (n : ℕ) : ℕ :=
  let P5 := pentagonal
  let P6 := hexagonal
  -- A practical upper bound for $x, y, z$ is $\lfloor\sqrt{n}\rfloor + 2$.
  -- Note: The bounds in the definition are for computation, mathematically the sum is over all natural numbers.
  -- However, since $x^2, P5(y), P6(z) \le n$, the coordinates are mathematically bounded.
  let max_coord_bound := n.sqrt + 2

  (Finset.range max_coord_bound).sum fun x =>
  (Finset.range max_coord_bound).sum fun y =>
  (Finset.range max_coord_bound).sum fun z =>
    if x^2 + P5 y + P6 z = n then 1 else 0


theorem a_zero : a 0 = 1 := by sorry

theorem a_one : a 1 = 3 := by sorry

theorem a_two : a 2 = 3 := by sorry

theorem a_three : a 3 = 1 := by sorry

/--
A160324: On Sep 04 2009, _Zhi-Wei Sun_ conjectured that the sequence contains every positive integer.
-/
theorem oeis_a160324_conjecture_3 : ∀ k : ℕ, 0 < k → ∃ n : ℕ, a n = k :=
  by sorry
