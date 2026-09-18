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
# Partitions of $n$ into $x + y$ with $x(x+1)/2 + y^2$ prime

Number of ways to write $n = x + y$ ($x, y > 0$) with $x(x+1)/2 + y^2$ prime.

*References:*
- [A228425](https://oeis.org/A228425)
-/

namespace OeisA228425

/-- Number of ways to write $n = x + y$ ($x, y > 0$) with $x(x+1)/2 + y^2$ prime. -/
def a (n : ℕ) : ℕ :=
  (Finset.Ico 1 n).filter (fun x : ℕ =>
    let y := n - x
    Nat.Prime (x * (x + 1) / 2 + y ^ 2)
  ) |>.card

/-- The $m$-gonal number $p_m(x) = (m-2)x(x-1)/2 + x$. -/
def polygonalNumber (m x : ℕ) : ℕ :=
  (m - 2) * x * (x - 1) / 2 + x

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture: $a(n) > 0$ for all $n > 1$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 1) : a n > 0 := by
  sorry

/--
We also conjecture that any integer $n > 1$ can be written as $x + y$ ($x, y > 0$) with
$p_k(x) + p_{k+1}(y)$ prime, if and only if $k$ is among $3, 39, 99$.
-/
@[category research open, AMS 11]
theorem conjecture2 (k : ℕ) (hk : 3 ≤ k) :
    (∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (polygonalNumber k x + polygonalNumber (k + 1) y)) ↔
    k = 3 ∨ k = 39 ∨ k = 99 := by
  sorry

/--
The pair $(k, m)$ works if $k$ is among $3, 4, 6$, and $m > k$ is not congruent to $k$ modulo $2$,
in the sense that all sufficiently large integers $n$ can be written as $x + y$ ($x, y > 0$) with
$p_k(x) + p_m(y)$ prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture3 (k m : ℕ) (hk : k = 3 ∨ k = 4 ∨ k = 6) (hm : k < m)
    (hmod : ¬ m ≡ k [MOD 2]) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (polygonalNumber k x + polygonalNumber m y) := by
  sorry

/--
For $k = 5$, the pair $(5, m)$ works (with $m > 5$) if $m$ is congruent to $0$ or $4$ modulo $6$,
in the sense that all sufficiently large integers $n$ can be written as $x + y$ ($x, y > 0$) with
$p_5(x) + p_m(y)$ prime.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture4 (m : ℕ) (hm : 5 < m) (hmod : m ≡ 0 [MOD 6] ∨ m ≡ 4 [MOD 6]) :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (polygonalNumber 5 x + polygonalNumber m y) := by
  sorry

/-- The set of pairs $(k, m)$ with $2 < k \le 10$ and $k < m \le 100$ conjectured by Zhi-Wei Sun
to satisfy the property that any $n > 1$ can be written as $x + y$ ($x, y > 0$) with
$p_k(x) + p_m(y)$ prime. -/
def sunPolygonalPairs : Finset (ℕ × ℕ) :=
  {(3, 4), (3, 6), (3, 28), (3, 46), (3, 52), (3, 82), (3, 88),
   (4, 7), (4, 15), (4, 25), (4, 27), (4, 37), (4, 43), (4, 63), (4, 67), (4, 97),
   (6, 25), (6, 43), (6, 73),
   (7, 10), (7, 18), (7, 100),
   (10, 15), (10, 19), (10, 27), (10, 37), (10, 55), (10, 75), (10, 79), (10, 87), (10, 99)}

/--
The only pairs $(k, m)$ with $2 < k \le 10$ and $k < m \le 100$ such that any integer $n > 1$ can
be written as $x + y$ ($x, y > 0$) with $p_k(x) + p_m(y)$ prime, are the $31$ pairs in
`sunPolygonalPairs`.
- Zhi-Wei Sun
-/
@[category research open, AMS 11]
theorem conjecture5 (k m : ℕ) (hk : 2 < k) (hk10 : k ≤ 10) (hm : k < m) (hm100 : m ≤ 100) :
    (∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (polygonalNumber k x + polygonalNumber m y)) ↔
    (k, m) ∈ sunPolygonalPairs := by
  sorry

end OeisA228425
