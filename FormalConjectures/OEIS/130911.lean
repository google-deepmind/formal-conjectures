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
# Odious primes minus evil primes among first $n$ primes

$a(n)$ is the number of primes with odd binary weight (odious primes) among the first $n$ primes
minus the number with even binary weight (evil primes).

*References:*
- [A130911](https://oeis.org/A130911)-/

namespace OeisA130911

/-- Parity sign of binary weight: $+1$ if popcount is odd, $-1$ if even. -/
def signWeight (k : ℕ) : ℤ :=
  if (Nat.digits 2 k).sum % 2 = 1 then 1 else -1

/-- $a(n) = \sum_{i=0}^{n-1} \mathrm{signWeight}(p_i)$ where $p_i$ is the $i$-th prime. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, signWeight (Nat.nth Nat.Prime i)

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  have h : Finset.range 1 = {0} := by decide
  rw [h, Finset.sum_singleton]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  rw [h0]
  decide +native

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by
  unfold a
  have h : Finset.range 2 = {0, 1} := by decide
  rw [h, Finset.sum_pair (by decide)]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  rw [h0, h1]
  decide +native

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = -1 := by
  unfold a
  have h : Finset.range 3 = {0, 1, 2} := by decide
  rw [h]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  rw [h0, h1, h2]
  decide +native

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  have h : Finset.range 4 = {0, 1, 2, 3} := by decide
  rw [h]
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h2 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have h3 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  rw [h0, h1, h2, h3]
  decide +native

/--
Shevelev conjectures that $a(n) \ge 0$ for $n > 3$.-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 3 < n) : a n ≥ 0 := by
  sorry

end OeisA130911
