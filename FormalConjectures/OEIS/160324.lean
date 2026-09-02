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
# Number of ways to express $n$ as sum of square, pentagonal, and hexagonal numbers

$$a(n) = |\{(x, y, z) \in \mathbb{N}^3 : x^2 + p_5(y) + p_6(z) = n\}|$$

*References:*
- [A160324](https://oeis.org/A160324)-/

namespace OeisA160324

/-- $p_k(x) = \frac{(k-2)x(x-1)}{2} + x$ is the $x$-th $k$-gonal number. -/
def polygonalNumber (k x : ℕ) : ℕ :=
  (k - 2) * (x * (x - 1) / 2) + x

/-- $p_5(y) = \frac{3y^2 - y}{2}$ is the $y$-th pentagonal number. -/
def pentagonal (y : ℕ) : ℕ := polygonalNumber 5 y

/-- $p_6(z) = 2z^2 - z$ is the $z$-th hexagonal number. -/
def hexagonal (z : ℕ) : ℕ := polygonalNumber 6 z

/-- Number of representations of $n$ as sum of square, pentagonal, and hexagonal numbers. -/
def a (n : ℕ) : ℕ :=
  let max_coord_bound := n.sqrt + 2
  ∑ x ∈ Finset.range max_coord_bound,
    ∑ y ∈ Finset.range max_coord_bound,
      ∑ z ∈ Finset.range max_coord_bound,
        if x ^ 2 + pentagonal y + hexagonal z = n then 1 else 0

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by decide +native

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 3 := by decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 3 := by decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide +native

/--
In April 2009, _Zhi-Wei Sun_ conjectured that $a(n) > 0$ for every $n = 0, 1, 2, 3, \dots$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) : 0 < a n := by
  sorry

/--
For each integer $m > 2$, any natural number $n$ can be written in the form
$p_{m+1}(x_1) + \cdots + p_{2m}(x_m)$ with $x_1, \dots, x_m$ nonnegative integers, where
$p_k(x) = (k-2)x(x-1)/2 + x$ ($x=0,1,2,\dots$) are $k$-gonal numbers.
- _Zhi-Wei Sun_, Aug 15 2009
-/
@[category research open, AMS 11]
theorem conjecture2 (m : ℕ) (hm : m > 2) (n : ℕ) :
    ∃ x : Fin m → ℕ, n = ∑ i : Fin m, polygonalNumber (m + (i : ℕ) + 1) (x i) := by
  sorry

/--
The sequence contains every positive integer.
- _Zhi-Wei Sun_, Sep 04 2009
-/
@[category research open, AMS 11]
theorem conjecture3 (k : ℕ) (hk : 0 < k) : ∃ n : ℕ, a n = k := by
  sorry

/--
Conjecture (Zhi-Wei Sun, Aug 21 2009):
For any integer $m > 2$, each natural number $n$ can be expressed as
$p_{m+1}(x_1) + p_{m+2}(x_2) + p_{m+3}(x_3) + r$ with $x_1, x_2, x_3 \in \mathbb{N}$ and
$r \in \{0, \dots, m-3\}$.
-/
@[category research open, AMS 11]
theorem conjecture4 (m : ℕ) (hm : 2 < m) (n : ℕ) :
    ∃ x1 x2 x3 r : ℕ, r ≤ m - 3 ∧
      n = polygonalNumber (m + 1) x1 + polygonalNumber (m + 2) x2 + polygonalNumber (m + 3) x3 + r := by
  sorry

/--
Conjecture (Zhi-Wei Sun, Aug 21 2009):
For each integer $m > 2$, all sufficiently large integers $n$ can be expressed in the form
$p_{m+1}(x_1) + p_{m+2}(x_2) + p_{m+3}(x_3)$ with $x_1, x_2, x_3 \in \mathbb{N}$.
-/
@[category research open, AMS 11]
theorem conjecture5 (m : ℕ) (hm : 2 < m) :
    ∀ᶠ n in Filter.atTop,
      ∃ x1 x2 x3 : ℕ, n = polygonalNumber (m + 1) x1 + polygonalNumber (m + 2) x2 + polygonalNumber (m + 3) x3 := by
  sorry

end OeisA160324

