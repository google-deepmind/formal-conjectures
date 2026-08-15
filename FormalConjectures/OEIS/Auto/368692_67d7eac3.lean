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

import FormalConjectures.Util.ProblemImports

open Nat

/--
A368692:
$$a(n) = \frac{(12n + 6)! \cdot (6n + 9)!}{108 \cdot (4n + 2)! \cdot (2n + 3)! \cdot ((6n + 5)!)^2}$$
It is conjectured that $a(n)$ are integers.
-/
def a (n : ℕ) : ℕ :=
  let num : ℕ := (12 * n + 6)! * (6 * n + 9)!
  let den_base : ℕ := (4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2
  num / (108 * den_base)


theorem a_zero : a 0 = 14 := by
  rfl

theorem a_one : a 1 = 563108 := by
  rfl

theorem a_two : a 2 = 54231252075 := by
  sorry

theorem a_three : a 3 = 6700034035890000 := by
  sorry


/--
Conjecture from OEIS A368692: $a(n)$ is an integer for all $n \in \mathbb{N}$.
According to A. Adolphson and S. Sperber, "On the integrality of hypergeometric series
whose coefficients are factorial ratios", ArXiv: 2001.03296, s.page 14, first equation
after Eq.(7.4): for any two integers K, L, the ratios $(3K)!(3L)!/(K!L!((K+L)!)^2)$
are proven to be integers. $108 \cdot a(n)$ results from $K = 4n+2$ and $L = 2n+3$, $n \ge 0$.
It is conjectured here that $a(n)$ are integers.
This is equivalent to the denominator dividing the numerator exactly in the definition
of $a(n)$.
-/
theorem oeis_a368692_conjecture_integrality (n : ℕ) :
  108 * ((4 * n + 2)! * (2 * n + 3)! * ((6 * n + 5)!)^2) ∣ (12 * n + 6)! * (6 * n + 9)! := by sorry
