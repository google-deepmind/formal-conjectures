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
# Sums of a triangular number and three weighted cubes

Number of ordered ways to write $n$ as $\frac{w(w+1)}{2} + x^3 + y^3 + 2z^3$ with $w > 0$,
$0 \le x \le y$, and $z \ge 0$.

*References:*
- [A262880](https://oeis.org/A262880)
-/

namespace OeisA262880

/-- The $w$-th triangular number $\frac{w(w+1)}{2}$. -/
def triangular (w : ℕ) : ℕ :=
  w * (w + 1) / 2

/--
Number of ordered ways to write $n$ as $\frac{w(w+1)}{2} + x^3 + y^3 + 2z^3$ with $w > 0$,
$0 \le x \le y$, and $z \ge 0$.
-/
def a (n : ℕ) : ℕ :=
  ∑ w ∈ Finset.Ico 1 (n + 1),
    ∑ x ∈ Finset.range (n + 1),
      ∑ y ∈ Finset.Ico x (n + 1),
        ∑ z ∈ Finset.range (n + 1),
          if triangular w + x ^ 3 + y ^ 3 + 2 * z ^ 3 == n then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 3 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 3 := by decide

/-- The set of coefficient pairs $(b, c)$ for part (i) of the conjecture. -/
def Pairs1 : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 3), (1, 4), (1, 6),
   (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 20), (2, 21), (2, 34),
   (3, 3), (3, 4), (3, 5), (3, 6),
   (4, 10)}

/--
Conjecture (i): Any positive integer can be written as $\frac{w(w+1)}{2} + x^3 + by^3 + cz^3$
with $w > 0$ and $x, y, z \ge 0$, provided that $(b, c) \in \{(1,2), (1,3), (1,4), (1,6),
(2,2), (2,3), (2,4), (2,5), (2,6), (2,7), (2,20), (2,21), (2,34), (3,3), (3,4), (3,5),
(3,6), (4,10)\}$.
-/
@[category research open, AMS 11]
theorem conjecture1 (p : ℕ × ℕ) (hp : p ∈ Pairs1) (n : ℕ) (hn : 0 < n) :
    ∃ w x y z : ℕ, 0 < w ∧ n = triangular w + x ^ 3 + p.1 * y ^ 3 + p.2 * z ^ 3 := by
  sorry

/-- The set of coefficient pairs $(b, c)$ for part (ii) of the conjecture. -/
def Pairs2 : Finset (ℕ × ℕ) :=
  {(3, 4), (3, 6), (4, 8)}

/--
Conjecture (ii): For $(b, c) \in \{(3,4), (3,6), (4,8)\}$, every nonnegative integer $n$ is of
the form $\frac{w(w+1)}{2} + 2x^3 + by^3 + cz^3$ for some nonnegative integers $w, x, y, z$.
-/
@[category research open, AMS 11]
theorem conjecture2 (p : ℕ × ℕ) (hp : p ∈ Pairs2) (n : ℕ) :
    ∃ w x y z : ℕ, n = triangular w + 2 * x ^ 3 + p.1 * y ^ 3 + p.2 * z ^ 3 := by
  sorry

end OeisA262880
