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
# Tug of war score between prime gap increases and decreases

Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases:
start with score $= 0$ at $n = 1$ and at stage $k > 1$, increase (resp. decrease) the score by $1$
if the $k$-th prime gap is greater (resp. less) than the previous prime gap.

*References:*
- [A092243](https://oeis.org/A092243)-/

namespace OeisA92243

/-- The $n$-th prime gap $g(n) = p_n - p_{n-1}$ for $n \ge 1$,
where $p_i$ is the $i$-th prime (0-indexed). -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n - Nat.nth Nat.Prime (n - 1)

/-- Score at stage $n$ in "tug of war" between prime gap increases vs. prime gap decreases. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n ≤ 1 then 0
  else
    ∑ k ∈ Finset.Icc 2 n,
      ((primeGap k : ℤ) - (primeGap (k - 1) : ℤ)).sign

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  unfold a
  have h2 : ¬ 2 ≤ 1 := by decide
  rw [if_neg h2]
  have h_icc : Finset.Icc 2 2 = {2} := by decide
  rw [h_icc, Finset.sum_singleton]
  unfold primeGap
  have h_zero : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h_one : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h_two : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  rw [h_zero, h_one, h_two]
  decide

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  unfold a
  have h3 : ¬ 3 ≤ 1 := by decide
  rw [if_neg h3]
  have h_icc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h_icc, Finset.sum_pair (by decide)]
  unfold primeGap
  have h_zero : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h_one : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
  have h_two : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  have h_three : Nat.nth Nat.Prime 3 = 7 := Nat.nth_prime_three_eq_seven
  rw [h_zero, h_one, h_two, h_three]
  decide

/--
Is the score $a(n) > 0$ for some $n > 250000$?-/
@[category research open, AMS 11]
theorem conjecture1 : answer(sorry) ↔ ∃ n > 250000, a n > 0 := by
  sorry

/--
Is the score $a(n)$ bounded from below?-/
@[category research open, AMS 11]
theorem conjecture2 : answer(sorry) ↔ ∃ B : ℤ, ∀ n : ℕ, B ≤ a n := by
  sorry

/--
Is the score $a(n)$ bounded from above?-/
@[category research open, AMS 11]
theorem conjecture3 : answer(sorry) ↔ ∃ B : ℤ, ∀ n : ℕ, a n ≤ B := by
  sorry

/--
Is the score $a(n) > 0$ for infinitely many values of $n$?-/
@[category research open, AMS 11]
theorem conjecture4 : answer(sorry) ↔ Set.Infinite {n : ℕ | a n > 0} := by
  sorry

/--
Is the score $a(n) < 0$ for infinitely many values of $n$?-/
@[category research open, AMS 11]
theorem conjecture5 : answer(sorry) ↔ Set.Infinite {n : ℕ | a n < 0} := by
  sorry

end OeisA92243
