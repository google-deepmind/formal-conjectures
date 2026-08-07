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
A338019: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $3x + 10y + 36z$ a positive square, where $x, y, z, w$ are nonnegative integers.
-/
def a (n : ℕ) : ℕ :=
  let M := n.sqrt
  let R := range (M + 1)
  -- Define the 4D bounded box BoundingBox = R x R x R x R, structured as ((ℕ × ℕ) × (ℕ × ℕ)).
  let BoundingBox := (R.product R).product (R.product R)

  Finset.card
    (BoundingBox.filter (fun p =>
      -- Destructure the nested tuple p : ((ℕ × ℕ) × (ℕ × ℕ))
      let ((x, y), (z, w)) := p

      -- Condition 1: x^2 + y^2 + z^2 + w^2 = n
      x^2 + y^2 + z^2 + w^2 = n ∧

      -- Condition 2: 3x + 10y + 36z is a positive perfect square
      let c := 3 * x + 10 * y + 36 * z
      -- Check if c > 0 AND c is a perfect square (c.sqrt * c.sqrt = c)
      c > 0 ∧ c.sqrt * c.sqrt = c
    ))

/-- Conjecture: a(n) > 0 if n is not divisible by 8. Moreover, a(n) = 0 if and only if n has the form $2^{4k+3} \cdot m$ ($k \ge 0$ and $m \in \{1, 3, 5, 61\}$). -/
theorem oeis_338019_conjecture_0 (n : ℕ) (h_n_pos : n > 0) :
  (a n = 0 ↔ ∃ k : ℕ, ∃ m : ℕ,
    (m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 61) ∧ n = 2^(4 * k + 3) * m) ∧
  (¬ (8 ∣ n) → a n > 0) :=
by sorry
