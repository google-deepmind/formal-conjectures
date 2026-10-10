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
# Ways to write $n = x + y + z$ with six linear and quadratic forms prime

Number of ways to write $n = x + y + z$ with $0 < x \le y \le z$ such that all the six numbers
$2x-1, 2y-1, 2z-1, 2xy-1, 2xz-1, 2yz-1$ are prime.

*References:*
- [A229969](https://oeis.org/A229969)
-/

namespace OeisA229969

/-- Number of ways to write $n = x + y + z$ with $0 < x \le y \le z$ such that all the six numbers
$2x-1, 2y-1, 2z-1, 2xy-1, 2xz-1, 2yz-1$ are prime. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.Icc 1 (n / 3),
    ∑ y ∈ Finset.Icc x ((n - x) / 2),
      let z := n - x - y
      if (2 * x - 1).Prime ∧ (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
         (2 * x * y - 1).Prime ∧ (2 * x * z - 1).Prime ∧ (2 * y * z - 1).Prime
      then 1 else 0

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by rfl

@[category test, AMS 11]
theorem a_5 : a 5 = 0 := by rfl

@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by rfl

/--
Conjecture: $a(n) > 0$ for all $n > 5$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 5) : a n > 0 := by
  sorry

/--
Moreover, any integer $n > 6$ can be written as $x + y + z$ with $x$ among $3, 4, 6, 10, 15$ such
that $2y-1, 2z-1, 2xy-1, 2xz-1, 2yz-1$ are prime.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) (hn : n > 6) :
    ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
      (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y - 1).Prime ∧ (2 * x * z - 1).Prime ∧ (2 * y * z - 1).Prime := by
  sorry

/--
Conjecture (i), part 1: Any integer $n > 6$ can be written as $x + y + z$ ($x, y, z > 0$) with
$2x-1, 2y-1, 2z-1$ and $2xyz-1$ all prime and $x$ among $2, 3, 4$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture3a (n : ℕ) (hn : n > 6) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({2, 3, 4} : Finset ℕ) ∧
      (2 * x - 1).Prime ∧ (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y * z - 1).Prime := by
  sorry

/--
Conjecture (i), part 2: Each integer $n > 2$ can be written as $x + y + z$ ($x, y, z > 0$) with
$2x+1, 2y+1, 2z+1$ and $2xyz+1$ all prime and $x$ among $1, 2, 3$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture3b (n : ℕ) (hn : n > 2) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 3} : Finset ℕ) ∧
      (2 * x + 1).Prime ∧ (2 * y + 1).Prime ∧ (2 * z + 1).Prime ∧
      (2 * x * y * z + 1).Prime := by
  sorry

/--
Conjecture (ii): Each integer $n > 4$ can be written as $x + y + z$ with $x = 3$ or $6$ such that
$2y+1, 2xyz-1$ and $2xyz+1$ are prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture4 (n : ℕ) (hn : n > 4) :
    ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (x = 3 ∨ x = 6) ∧
      (2 * y + 1).Prime ∧ (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime := by
  sorry

/--
Conjecture (iii), part 1: Every integer $n > 5$ can be written as $x + y + z$ ($x, y, z > 0$) with
$xy-1, xz-1, yz-1$ all prime and $x$ among $2, 6, 10$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture5a (n : ℕ) (hn : n > 5) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({2, 6, 10} : Finset ℕ) ∧
      (x * y - 1).Prime ∧ (x * z - 1).Prime ∧ (y * z - 1).Prime := by
  sorry

/--
Conjecture (iii), part 2: Any integer $n > 2$ not equal to $16$ can be written as $x + y + z$
($x, y, z > 0$) with $xy+1, xz+1, yz+1$ all prime and $x$ among $1, 2, 6$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture5b (n : ℕ) (hn : n > 2) (hne : n ≠ 16) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 6} : Finset ℕ) ∧
      (x * y + 1).Prime ∧ (x * z + 1).Prime ∧ (y * z + 1).Prime := by
  sorry

end OeisA229969
