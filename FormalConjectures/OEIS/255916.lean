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
# Representations of $n$ as a sum of generalized heptagonal, octagonal, and nonagonal numbers

The sequence $a(n)$ counts the number of ways to write $n$ as the sum of a generalized heptagonal
number $G_7(k) = \frac{5k^2 - 3k}{2}$ ($k \in \mathbb{Z}$), an octagonal number
$P_8(x) = x(3x - 2)$ ($x \ge 0$), and a nonagonal number $P_9(y) = \frac{y(7y - 5)}{2}$ ($y \ge 0$).

*References:*
- [A255916](https://oeis.org/A255916)
-/

namespace OeisA255916

open Nat Int Finset

/-- The primary sequence $a(n)$: number of ways to write $n$ as the sum of a generalized heptagonal
number, an octagonal number, and a nonagonal number. -/
def a (n : ℕ) : ℕ :=
  let generalizedHeptagonalNum (k : ℤ) : ℕ := ((5 * k ^ 2 - 3 * k) / 2).toNat
  let octagonalNum (x : ℕ) : ℕ := x * (3 * x - 2)
  let nonagonalNum (y : ℕ) : ℕ := y * (7 * y - 5) / 2
  let nBound : ℕ := n + 1
  let zBoundPos : ℤ := nBound
  let kSet : Finset ℤ := Finset.Icc (-zBoundPos) zBoundPos
  let xSet : Finset ℕ := Finset.range nBound
  let ySet : Finset ℕ := Finset.range nBound
  ∑ k ∈ kSet, ∑ x ∈ xSet, ∑ y ∈ ySet,
    if generalizedHeptagonalNum k + octagonalNum x + nonagonalNum y = n then 1 else 0

/-- The $m$-th generalized polygonal number $G_m(k) = \frac{(m-2)k^2 - (m-4)k}{2}$ for
$k \in \mathbb{Z}$. -/
def generalizedPolygonalNumOfSides (m : ℕ) (k : ℤ) : ℕ :=
  if 3 ≤ m then
    let m' := (m : ℤ)
    let val := (m' - 2) * k ^ 2 - (m' - 4) * k
    (val / 2).toNat
  else 0

/-- The $m$-th polygonal number $P_m(x) = \frac{(m-2)x^2 - (m-4)x}{2}$ for $x \in \mathbb{N}$. -/
def polygonalNumOfSides (m : ℕ) (x : ℕ) : ℕ :=
  if 3 ≤ m then
    let m' := (m : ℤ)
    let x' := (x : ℤ)
    let val := (m' - 2) * x' ^ 2 - (m' - 4) * x'
    (val / 2).toNat
  else 0

/-- Predicate asserting that $n$ can be written as the sum of a generalized $m$-gonal number
and two polygonal numbers $P_j$ and $P_k$. -/
def IsSumOfGmPjPk (m n j k : ℕ) : Prop :=
  ∃ (z : ℤ) (x y : ℕ),
    generalizedPolygonalNumOfSides m z + polygonalNumOfSides j x + polygonalNumOfSides k y = n

/-- The set of ordered pairs $(j, k)$ from part (i) of Sun's conjecture. -/
def sunPolygonalPairsSet1 : Finset (ℕ × ℕ) :=
  let kValsJ3 : Finset ℕ := (Icc 3 19) ∪ (Icc 21 24) ∪ {26, 27, 29, 30}
  let set3K := kValsJ3.image (fun k => (3, k))
  let kValsJ4 : Finset ℕ := (Icc 4 11) ∪ {13, 14, 17, 19, 20, 23, 26}
  let set4K := kValsJ4.image (fun k => (4, k))
  set3K ∪ set4K ∪ {(5, 6), (5, 9), (6, 7), (8, 9)}

/-- The set of ordered pairs $(j, k)$ from part (ii) of Sun's conjecture. -/
def sunPolygonalPairsSet2 : Finset (ℕ × ℕ) :=
  let kValsJ3 : Finset ℕ := (Icc 3 20) ∪ {22, 24, 25} ∪ (Icc 28 30) ∪ {32, 37}
  let set3K := kValsJ3.image (fun k => (3, k))
  let kValsJ4 : Finset ℕ :=
    (Icc 4 13) ∪ {15, 16, 18} ∪ (Icc 20 25) ∪ {27, 28, 31, 33, 34}
  let set4K := kValsJ4.image (fun k => (4, k))
  let kValsJ5 : Finset ℕ := (Icc 6 12) ∪ {20}
  let set5K := kValsJ5.image (fun k => (5, k))
  let kValsJ6 : Finset ℕ := Icc 7 10
  let set6K := kValsJ6.image (fun k => (6, k))
  set3K ∪ set4K ∪ set5K ∪ set6K ∪ {(7, 9), (7, 11), (8, 10), (9, 11)}

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by native_decide

@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by native_decide

@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by native_decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by native_decide

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
Conjecture (i): For $k \ge j \ge 3$, every nonnegative integer can be written as the sum of a
generalized heptagonal number, a $j$-gonal number and a $k$-gonal number, if and only if $(j, k)$
is among the following ordered pairs:
$(3, k)$ ($k = 3..19, 21..24, 26, 27, 29, 30$),
$(4, k)$ ($k = 4..11, 13, 14, 17, 19, 20, 23, 26$),
$(5, 6), (5, 9), (6, 7), (8, 9)$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (j k : ℕ) (hjk : 3 ≤ j ∧ j ≤ k) :
    (∀ n : ℕ, IsSumOfGmPjPk 7 n j k) ↔ (j, k) ∈ sunPolygonalPairsSet1 := by
  sorry

/--
Conjecture (ii): For $k \ge j \ge 3$, every nonnegative integer can be written as the sum of a
generalized pentagonal number, a $j$-gonal number and a $k$-gonal number, if and only if $(j, k)$
is among the following ordered pairs:
$(3, k)$ ($k = 3..20, 22, 24, 25, 28..30, 32, 37$),
$(4, k)$ ($k = 4..13, 15, 16, 18, 20..25, 27, 28, 31, 33, 34$),
$(5, k)$ ($k = 6..12, 20$), $(6, k)$ ($k = 7..10$), $(7, 9), (7, 11), (8, 10), (9, 11)$.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture3 (j k : ℕ) (hjk : 3 ≤ j ∧ j ≤ k) :
    (∀ n : ℕ, IsSumOfGmPjPk 5 n j k) ↔ (j, k) ∈ sunPolygonalPairsSet2 := by
  sorry

end OeisA255916
