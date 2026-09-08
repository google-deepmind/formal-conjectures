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
# Sum of next $n$ primes

The sum of the primes in the $n$-th row of the prime number triangle:
$$a(n) = \sum_{i = 1 + n(n-1)/2}^{n + n(n-1)/2} p_i$$
with $a(0) = 0$.

*References:*
- [A007468](https://oeis.org/A007468)
-/

namespace OeisA7468

/-- Sum of the next $n$ primes, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  let startIdx : ℕ := (n * (n - 1)) / 2
  ∑ i ∈ Finset.range n, Nat.nth Nat.Prime (startIdx + i)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  dsimp [a]
  rw [Finset.sum_singleton, add_zero, Nat.nth_prime_zero_eq_two]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 8 := by
  dsimp [a]
  rw [Finset.sum_range_succ, Finset.sum_range_one, add_zero, Nat.nth_prime_one_eq_three,
    show (1 + 1 : ℕ) = 2 by rfl, Nat.nth_prime_two_eq_five]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 31 := by
  dsimp [a]
  have h5 : Nat.nth Nat.Prime 5 = 13 := Nat.nth_count (by decide : Nat.Prime 13)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, add_zero,
    Nat.nth_prime_three_eq_seven, show (3 + 1 : ℕ) = 4 by rfl, Nat.nth_prime_four_eq_eleven,
    show (3 + 2 : ℕ) = 5 by rfl, h5]

/--
The only positive integer $n$ such that $a(n)$ is a perfect square is $n=38$.
- Carlos Eduardo Olivieri, Mar 09 2015
-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) (hsq : IsSquare (a n)) : n = 38 := by
  sorry

end OeisA7468
