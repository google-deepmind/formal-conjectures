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
# Partitions of $n$ into $x + y$ with $(xy)^2 + 1$ prime

Number of ways to write $n = x + y$ ($0 < x \le y$) with $(xy)^2 + 1$ prime.

*References:*
- [A219791](https://oeis.org/A219791)
-/

namespace OeisA219791

/-- Number of ways to write $n = x + y$ ($0 < x \le y$) with $(xy)^2 + 1$ prime. -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 2)).filter (fun x : ℕ => Nat.Prime ((x * (n - x)) ^ 2 + 1)) |>.card

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by decide

@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by decide

@[category test, AMS 11]
theorem a_5 : a 5 = 2 := by decide

/--
Conjecture: $a(n) > 0$ if $n$ is different from $1, 6, 16, 24$.
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) (hn : n > 0) (h1 : n ≠ 1) (h6 : n ≠ 6) (h16 : n ≠ 16) (h24 : n ≠ 24) :
    a n > 0 := by
  sorry

/--
Conjecture: For any positive integer $k$, each
sufficiently large integer $n$ can be written as $x + y$ ($x > 0, y > 0$) with $(xy)^{2^k} + 1$
prime.
- _Zhi-Wei Sun_
-/
@[category research open, AMS 11]
theorem conjecture2 (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime ((x * y) ^ (2 ^ k) + 1) := by
  sorry

end OeisA219791
