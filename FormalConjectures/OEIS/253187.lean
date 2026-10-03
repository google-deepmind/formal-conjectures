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
# Representations of $n$ as the sum of two pentagonal and a generalized decagonal number

The sequence $a(n)$ counts the number of ordered ways to write $n$ as the sum of a pentagonal
number $\frac{x(3x-1)}{2}$ ($x \ge 0$), a second pentagonal number $\frac{y(3y+1)}{2}$ ($y \ge 0$),
and a generalized decagonal number $m(4m-3)$ ($m \in \mathbb{Z}$).

*References:*
- [A253187](https://oeis.org/A253187)
-/

namespace OeisA253187

open Nat Finset

/-- The $x$-th pentagonal number $\frac{x(3x-1)}{2}$ for $x \ge 0$. -/
def pentagonalFirst (x : ℕ) : ℕ :=
  (x * (3 * x - 1)) / 2

/-- The $y$-th second pentagonal number $\frac{y(3y+1)}{2}$ for $y \ge 0$. -/
def pentagonalSecond (y : ℕ) : ℕ :=
  (y * (3 * y + 1)) / 2

/-- Returns $1$ if $r$ is a generalized decagonal number $m(4m-3)$ for some $m \in \mathbb{Z}$
(equivalently, $16r + 9$ is a perfect square), and $0$ otherwise. -/
def countGeneralizedDecagonalIndex (r : ℕ) : ℕ :=
  if Nat.sqrt (16 * r + 9) * Nat.sqrt (16 * r + 9) = 16 * r + 9 then 1 else 0

/-- The primary sequence $a(n)$: number of ordered ways to write $n$ as the sum of a pentagonal
number, a second pentagonal number, and a generalized decagonal number. -/
def a (n : ℕ) : ℕ :=
  ∑ x ∈ range (n + 1), ∑ y ∈ range (n + 1),
    let sumPent := pentagonalFirst x + pentagonalSecond y
    if sumPent ≤ n then
      countGeneralizedDecagonalIndex (n - sumPent)
    else
      0

/-- Generalized $k$-gonal number formula $\frac{(k-2)z^2 - (k-4)z}{2}$ for $z \in \mathbb{Z}$. -/
def polygonalNumVal (k : ℕ) (z : ℤ) : ℤ :=
  if 3 ≤ k then
    let k' : ℤ := k
    ((k' - 2) * z * z - (k' - 4) * z) / 2
  else 0

/-- The $k$-gonal number (first type) for index $x \in \mathbb{N}$. -/
def pKFirst (k : ℕ) (x : ℕ) : ℕ :=
  (polygonalNumVal k (x : ℤ)).toNat

/-- The second $k$-gonal number for index $y \in \mathbb{N}$. -/
def pKSecond (k : ℕ) (y : ℕ) : ℕ :=
  (polygonalNumVal k (-(y : ℤ))).toNat

/-- The set of pairs $(k, m)$ appearing in Sun's universal sum conjecture. -/
def cPairs : Set (ℕ × ℕ) :=
  {(5, 7), (5, 9), (5, 13), (6, 5), (6, 7), (7, 5)}

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 2 := by native_decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by native_decide

/--
Conjecture: $a(n) > 0$ for all $n$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) : 0 < a n := by
  sorry

/--
Conjecture: For any ordered pair $(k, m)$ among $(5,7), (5,9), (5,13), (6,5), (6,7), (7,5)$,
each nonnegative integer $n$ can be written as the sum of a $k$-gonal number, a second $k$-gonal
number, and a generalized $m$-gonal number.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (k m : ℕ) (hkm : (k, m) ∈ cPairs) (n : ℕ) :
    ∃ x y : ℕ, ∃ z : ℤ,
      pKFirst k x + pKSecond k y + (polygonalNumVal m z).toNat = n := by
  sorry

end OeisA253187
