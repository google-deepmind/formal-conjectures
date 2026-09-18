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
# Ways to write $n = x + y$ with $nx + y$ and $ny - x$ both prime

Number of ways to write $n = x + y$ ($x, y > 0$) with $nx + y$ and $ny - x$ both prime.

*References:*
- [A232194](https://oeis.org/A232194)
-/

namespace OeisA232194

/-- Number of ways to write $n = x + y$ ($x, y > 0$) with $nx + y$ and $ny - x$ both prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Ico 1 n,
    let y := n - x
    if (n * x + y).Prime ∧ (n * y - x).Prime then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by rfl

/--
Conjecture (i), part 1: $a(n) > 0$ for all $n > 2$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 2) : a n > 0 := by
  sorry

/--
Conjecture (i), part 2: $a(n) = 1$ only for $n = 3, 4, 6, 20, 24$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    a n = 1 ↔ n ∈ ({3, 4, 6, 20, 24} : Finset ℕ) := by
  sorry

/--
Conjecture (ii): Any positive integer $n$ not among $1, 30, 54$ can be written as $x + y$
($x, y > 0$) with $nx + y$ and $ny + x$ both prime.
-/
@[category research open, AMS 11]
theorem conjecture3 (n : ℕ) (hn : n > 0) (hne : n ∉ ({1, 30, 54} : Finset ℕ)) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (n * x + y).Prime ∧ (n * y + x).Prime := by
  sorry

/--
Conjecture (iii): Each integer $n > 1$ not equal to $8$ can be expressed as $x + y$ ($x, y > 0$)
with $nx^2 + y$ prime.
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : n > 1) (hne : n ≠ 8) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x ^ 2 + y).Prime := by
  sorry

/--
Conjecture (iii), variant: Each integer $n > 1$ not equal to $8$ can be expressed as $x + y$
($x, y > 0$) with $x^4 + ny$ prime.
-/
@[category research open, AMS 11]
theorem conjecture5 (n : ℕ) (hn : n > 1) (hne : n ≠ 8) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + n * y).Prime := by
  sorry

/--
Conjecture (iv): Any integer $n > 5$ can be written as $p + q$ ($q > 0$) with $p$ and $nq^2 + 1$
both prime.
-/
@[category research open, AMS 11]
theorem conjecture6 (n : ℕ) (hn : n > 5) :
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧ p.Prime ∧ (n * q ^ 2 + 1).Prime := by
  sorry

end OeisA232194
