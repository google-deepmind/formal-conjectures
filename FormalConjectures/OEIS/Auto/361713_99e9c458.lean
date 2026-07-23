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

open Finset Nat

/--
A361713: The sequence defined by
$$a(n) = \sum_{k = 0}^{n-1} \binom{n}{k}^2 \binom{n+k-1}{k}^2$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2


theorem a_zero : a 0 = 0 := by
  rfl

theorem a_one : a 1 = 1 := by
  rfl

theorem a_two : a 2 = 17 := by
  rfl

theorem a_three : a 3 = 406 := by
  rfl

/--
Conjecture 2: for $r \ge 2$, the supercongruence $a(p^r) \equiv a(p^{r-1}) \pmod{p^{4r+1}}$ holds for all primes $p \ge 7$.
-/
theorem oeis_361713_conjecture_2 (p r : ℕ) :
  Nat.Prime p →
  p ≥ 7 →
  r ≥ 2 →
  a (p ^ r) ≡ a (p ^ (r - 1)) [MOD (p ^ (4 * r + 1))] :=
by sorry
