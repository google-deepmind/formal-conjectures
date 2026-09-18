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
# Sums of a cube, a square, and a positive triangular number

Number of ordered ways to write $n$ as $x^3 + y^2 + \frac{z(z+1)}{2}$ with $x \ge 0$, $y \ge 0$,
and $z > 0$.

*References:*
- [A262813](https://oeis.org/A262813)
-/

namespace OeisA262813

/-- The $z$-th triangular number $\frac{z(z+1)}{2}$. -/
def triangular (z : ℕ) : ℕ :=
  z * (z + 1) / 2

/--
Number of ordered ways to write $n$ as $x^3 + y^2 + \frac{z(z+1)}{2}$ with $x \ge 0$, $y \ge 0$,
and $z > 0$.
-/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (n + 1),
    ∑ y ∈ Finset.range (n + 1),
      ∑ z ∈ Finset.Ico 1 (n + 1),
        if x ^ 3 + y ^ 2 + triangular z == n then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/-- The set of exceptional positive integers $n$ for which $a(n) = 1$. -/
def Singletons : Finset ℕ :=
  {1, 9, 21, 35, 98, 152, 306}

/--
Conjecture: $a(n) > 0$ for all $n > 0$, and $a(n) = 1$ only for
$n = 1, 9, 21, 35, 98, 152, 306$.
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    0 < a n ∧ (a n = 1 ↔ n ∈ Singletons) := by
  sorry

end OeisA262813
