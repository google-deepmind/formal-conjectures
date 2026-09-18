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
# Recurrence $a(n+1) = 2n(n+1)a(n) - n^4 a(n-1)$ and associated polynomials

The sequence $a(n)$ is defined by $a(0) = 1$, $a(1) = 0$, and
$a(n+1) = 2n(n+1)a(n) - n^4 a(n-1)$ for $n > 0$.
The associated polynomials $S_n(x) \in \mathbb{Z}[x]$ satisfy $S_0(x) = 1$, $S_1(x) = x$, and
$S_{n+1}(x) = (x + 2n(n+1)) S_n(x) - n^4 S_{n-1}(x)$ for $n > 0$.

*References:*
- [A217703](https://oeis.org/A217703)
-/

namespace OeisA217703

/-- `a n` is the sequence defined by $a(0)=1$, $a(1)=0$, and
$a(n+1) = 2n(n+1)a(n) - n^4 a(n-1)$ for $n > 0$. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | k + 2 =>
    let m : ℤ := k + 1
    (2 * m * (m + 1)) * a (k + 1) - (m ^ 4) * a k

/-- `polyS n` is the polynomial $S_n(x)$ defined by $S_0(x) = 1$, $S_1(x) = x$, and
$S_{n+1}(x) = (x + 2n(n+1)) S_n(x) - n^4 S_{n-1}(x)$ for $n > 0$. -/
noncomputable def polyS : ℕ → Polynomial ℤ
  | 0 => 1
  | 1 => Polynomial.X
  | k + 2 =>
    let m : ℤ := k + 1
    (Polynomial.X + Polynomial.C (2 * m * (m + 1))) * polyS (k + 1) -
      Polynomial.C (m ^ 4) * polyS k

@[category test, AMS 11]
theorem a_0 : a 0 = 1 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = -1 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = -12 := by rfl

@[category test, AMS 11]
theorem a_4 : a 4 = -207 := by rfl

/--
Conjecture, (i): $S_n(x)$ is irreducible over the field of rational numbers
for every $n = 1, 2, 3, \dots$
- Zhi-Wei Sun, Mar 20 2013
-/
@[category research open, AMS 11 12]
theorem conjecture1 (n : ℕ) (hn : 1 ≤ n) :
    Irreducible (Polynomial.map (Int.castRingHom ℚ) (polyS n)) := by
  sorry

/--
Conjecture, (ii): $a(n) = S_n(0)$ is negative if and only if
$1 < n < 58$ or $n > 2177$.
-/
@[category research open, AMS 11]
theorem conjecture2 (n : ℕ) :
    a n < 0 ↔ (1 < n ∧ n < 58) ∨ 2177 < n := by
  sorry

/--
Conjecture, (iii): $|a(n)|^{1/n} = o(n^2)$ as $n$ tends to infinity.
-/
@[category research open, AMS 11 26]
theorem conjecture3 :
    Filter.Tendsto (fun n : ℕ => |(a n : ℝ)| ^ (1 / (n : ℝ)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  sorry

end OeisA217703
