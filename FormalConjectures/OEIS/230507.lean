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

import FormalConjecturesUtil

/-!
# Triples summing to $n$ with $2m+1$ and $2m^3+1$ prime

Number of ways to write $n = x + y + z$ with $x \le y \le z$, where $x, y, z$ are positive integers
such that $2m + 1$ and $2m^3 + 1$ are both prime for $m \in \{x, y, z\}$.

*References:*
- [A230507](https://oeis.org/A230507)
-/

namespace OeisA230507

/-- Number of ways to write $n = x + y + z$ with $x \le y \le z$, where $x, y, z$ are numbers $m$
with $2m + 1$ and $2m^3 + 1$ both prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 (n / 3),
    ∑ y ∈ Finset.Icc x ((n - x) / 2),
      let z := n - x - y
      if (2 * x + 1).Prime ∧ (2 * x ^ 3 + 1).Prime ∧
         (2 * y + 1).Prime ∧ (2 * y ^ 3 + 1).Prime ∧
         (2 * z + 1).Prime ∧ (2 * z ^ 3 + 1).Prime
      then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by rfl

/--
Conjecture (i): $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 2) : a n > 0 := by
  sorry

/--
Conjecture (ii): Any integer $n > 8$ can be written as $x + y + z$ ($x, y, z > 0$) with
$2x + 1, 2y + 1, 2z - 1, 2x^4 - 1, 2y^4 - 1, 2z^4 - 1$ all prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 8) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (2 * x + 1).Prime ∧ (2 * y + 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x ^ 4 - 1).Prime ∧ (2 * y ^ 4 - 1).Prime ∧ (2 * z ^ 4 - 1).Prime := by
  sorry

end OeisA230507
