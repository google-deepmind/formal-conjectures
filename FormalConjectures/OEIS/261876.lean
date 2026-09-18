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
# Refining Lagrange's four-square theorem with $(5x^2 + 7y^2 + 9z^2)yz$ a square

Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2 + 7y^2 + 9z^2)yz$
a square, where $x, y, z, w$ are nonnegative integers with $z > 0$.

*References:*
- [A261876](https://oeis.org/A261876)
- [Refining Lagrange's four-square theorem](https://arxiv.org/abs/1604.06723)
  by *Zhi-Wei Sun*, arXiv:1604.06723 (2016)
-/

namespace OeisA261876

/-- Whether a natural number $k$ is a perfect square. -/
def isSquare (k : ℕ) : Bool :=
  Nat.sqrt k ^ 2 == k

/--
Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $(5x^2 + 7y^2 + 9z^2)yz$
a square, where $x, y, z, w$ are nonnegative integers with $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (n + 1),
    ∑ y ∈ Finset.range (n + 1),
      ∑ z ∈ Finset.Ico 1 (n + 1),
        ∑ w ∈ Finset.range (n + 1),
          if x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 == n &&
             isSquare ((5 * x ^ 2 + 7 * y ^ 2 + 9 * z ^ 2) * y * z) then
            1
          else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by native_decide

/-- The set of base integers $m$ for which $a(n) = 1$ when $n = 4^k m$. -/
def SpecialSet : Finset ℕ :=
  {1, 7, 23, 647, 863}

/--
Conjecture (i): $a(n) > 0$ for all $n > 0$, and $a(n) = 1$ only for $n = 4^k m$
($k = 0, 1, 2, \dots$ and $m \in \{1, 7, 23, 647, 863\}$).
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) :
    (0 < n → 0 < a n) ∧
    (a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ SpecialSet, n = 4 ^ k * m) := by
  sorry

/-- The set of coefficient triples $(c_1, c_2, c_3)$ for part (ii) of the conjecture. -/
def Triples : Finset (ℕ × ℕ × ℕ) :=
  {(1, 8, 20), (3, 5, 15), (6, 14, 4), (7, 29, 5), (18, 38, 18), (39, 81, 51), (42, 98, 14)}

/--
Conjecture (ii): For each triple $(c_1, c_2, c_3) \in \{(1,8,20), (3,5,15), (6,14,4), (7,29,5),
(18,38,18), (39,81,51), (42,98,14)\}$, any natural number can be written as
$x^2 + y^2 + z^2 + w^2$ with $x, y, z, w$ nonnegative integers such that
$xy(c_1 x^2 + c_2 y^2 + c_3 z^2)$ is a square.
-/
@[category research open, AMS 11]
theorem conjecture2 (t : ℕ × ℕ × ℕ) (ht : t ∈ Triples) (n : ℕ) :
    ∃ x y z w : ℕ, n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧
      IsSquare (x * y * (t.1 * x ^ 2 + t.2.1 * y ^ 2 + t.2.2 * z ^ 2)) := by
  sorry

end OeisA261876
