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
# Primorial squared plus one

The sequence $a(n)$ is defined by $a(n) = (p_n\#)^2 + 1$, where $p_n\# = \prod_{k=0}^{n-1} p_k$
is the $n$-th primorial (A002110).

*References:*
- [A189409](https://oeis.org/A189409)
-/

namespace OeisA189409

/-- The sequence $a(n) = (\prod_{k=0}^{n-1} p_k)^2 + 1$. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, Nat.nth Nat.Prime k) ^ 2 + 1

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 2 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 5 := by
  unfold a
  rw [Finset.prod_range_one, Nat.nth_prime_zero_eq_two]
  rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 37 := by
  unfold a
  rw [Finset.prod_range_succ, Finset.prod_range_one,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  rfl

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 901 := by
  unfold a
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one,
    Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
  rfl

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 44101 := by
  unfold a
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_one, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
  rfl

/--
It is unknown whether or not numbers in this sequence are always squarefree.
- _John M. Campbell_, Apr 21 2011
-/
@[category research open, AMS 11]
theorem conjecture1 (n : ℕ) : Squarefree (a n) := by
  sorry

/--
It is unknown whether or not there exist infinitely many primes in this sequence.
- _John M. Campbell_, Apr 21 2011
-/
@[category research open, AMS 11]
theorem conjecture2 : Set.Infinite {n : ℕ | (a n).Prime} := by
  sorry

end OeisA189409
