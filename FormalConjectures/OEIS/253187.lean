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
module

public import FormalConjecturesUtil

/-!
# Representations of $n$ as the sum of two pentagonal and a generalized decagonal number

The sequence $a(n)$ counts the number of ordered ways to write $n$ as the sum of a pentagonal
number $\frac{x(3x-1)}{2}$ ($x \ge 0$), a second pentagonal number $\frac{y(3y+1)}{2}$ ($y \ge 0$),
and a generalized decagonal number $m(4m-3)$ ($m \in \mathbb{Z}$).

*References:*
- [A253187](https://oeis.org/A253187)
-/

@[expose] public section

namespace OeisA253187

open Nat Finset

/-- Returns $1$ if $r$ is a generalized decagonal number $m(4m-3)$ for some $m \in \mathbb{Z}$
(equivalently, $16r + 9$ is a perfect square), and $0$ otherwise. -/
def countGeneralizedDecagonalIndex (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/-- Number of ordered ways to write $n$ as the sum of a pentagonal
number, a second pentagonal number, and a generalized decagonal number. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ range (n + 1), ∑ y ∈ range (n + 1),
    let sumPent := Nat.polygonalNumber 5 x + Nat.generalizedPolygonalNumber 5 (-(y : ℤ))
    if sumPent ≤ n then
      countGeneralizedDecagonalIndex (n - sumPent)
    else
      0

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide +kernel

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by decide +kernel

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide +kernel

/-- The set of pairs $(k, m)$ appearing in Sun's universal sum conjecture. -/
def cPairs : Set (ℕ × ℕ) :=
  {(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)}

/--
Conjecture: $a(n) > 0$ for all $n$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture_1 (n : ℕ) : 0 < a n := by
  sorry

/--
Conjecture: For any ordered pair $(k, m)$ among $(5,7), (5,9), (5,13), (6,5), (6,7), (7,5)$,
each nonnegative integer $n$ can be written as the sum of a $k$-gonal number, a second $k$-gonal
number, and a generalized $m$-gonal number.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture_2 (k m : ℕ) (hkm : (k, m) ∈ cPairs) (n : ℕ) :
    ∃ x y : ℕ, ∃ z : ℤ,
      Nat.polygonalNumber k x + Nat.generalizedPolygonalNumber k (-(y : ℤ)) +
        Nat.generalizedPolygonalNumber m z = n := by
  sorry

end OeisA253187
