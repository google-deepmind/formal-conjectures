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

open Nat Finset

/--
A333562: $a(n) = \sum_{j = 0}^{3n} \binom{n+j-1}{j} 2^j$.
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (3 * n + 1)) fun j =>
    (n + j - 1).choose j * (2 ^ j)


theorem a_zero : a 0 = 1 := by sorry
theorem a_one : a 1 = 15 := by sorry
theorem a_two : a 2 = 769 := by sorry
theorem a_three : a 3 = 47103 := by sorry

/--
We conjecture that this sequence satisfies the congruences
$a(n \cdot p^k) \equiv a(n \cdot p^{k-1}) \pmod{p^{3k}}$
for prime $p \ge 5$ and positive integers $n$ and $k$.
-/
theorem oeis_333562_conjecture_0_congruence (p n k : ℕ) :
    Nat.Prime p → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (3 * k)] := by
  sorry
