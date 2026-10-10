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
# Sums of a square and three weighted cubes

Number of ordered ways to write $n$ as $w^2 + x^3 + 2y^3 + 3z^3$, where $w, x, y$ and $z$ are
nonnegative integers.

*References:*
- [A262824](https://oeis.org/A262824)
-/

namespace OeisA262824

/--
Number of ordered ways to write $n$ as $w^2 + x^3 + 2y^3 + 3z^3$ with nonnegative integers
$w, x, y, z$.
-/
def a (n : ℕ) : ℕ :=
  ∑ w ∈ Finset.range (n + 1),
    ∑ x ∈ Finset.range (n + 1),
      ∑ y ∈ Finset.range (n + 1),
        ∑ z ∈ Finset.range (n + 1),
          if w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 == n then 1 else 0

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 4 := by decide

/--
Conjecture (i): For any $m \in \{3, 4, 5, 6\}$ and $n \ge 0$, there are nonnegative integers
$w, x, y, z$ such that $n = w^2 + x^3 + 2y^3 + mz^3$.
-/
@[category research open, AMS 11]
theorem conjecture1 (m : ℕ) (hm : m ∈ ({3, 4, 5, 6} : Finset ℕ)) (n : ℕ) :
    ∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + m * z ^ 3 := by
  sorry

/--
Conjecture (ii): For each polynomial $P(w, x, y, z) \in \{w^2 + x^3 + 2y^3 + z^4,
w^2 + x^3 + 2y^3 + 3z^4, w^2 + x^3 + 2y^3 + 6z^4, 2w^2 + x^3 + 4y^3 + z^4\}$, every
nonnegative integer $n$ is of the form $P(w, x, y, z)$ for some nonnegative integers $w, x, y, z$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    (∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + z ^ 4) ∧
    (∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4) ∧
    (∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 6 * z ^ 4) ∧
    (∃ w x y z : ℕ, n = 2 * w ^ 2 + x ^ 3 + 4 * y ^ 3 + z ^ 4) := by
  sorry

end OeisA262824
