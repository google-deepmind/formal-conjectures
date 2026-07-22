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
import Mathlib.Data.Nat.Prime.Nth

/-!
# Triangular matchstick numbers in the class of prime numbers

$a(n) = \sum_{k = n}^{2n} p_k$, where $p_k$ is the $k$-th prime.

*References:*
- [A105720](https://oeis.org/A105720)
-/

namespace OeisA105720

open Nat Finset

/--
The primary defining sequence `a`.
$a(n)$ is the sum of primes from the $n$-th prime to the $2n$-th prime, with $p_1=2$.
For $n=0$, we define $a(0) = 0$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else ∑ i ∈ Ico (n - 1) (2 * n), Nat.nth Nat.Prime i

@[category API, AMS 11]
lemma nth_prime_five : Nat.nth Nat.Prime 5 = 13 := by
  have h1 : Nat.count Nat.Prime 13 = 5 := by decide
  have h2 : Nat.Prime 13 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_six : Nat.nth Nat.Prime 6 = 17 := by
  have h1 : Nat.count Nat.Prime 17 = 6 := by decide
  have h2 : Nat.Prime 17 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

@[category API, AMS 11]
lemma nth_prime_seven : Nat.nth Nat.Prime 7 = 19 := by
  have h1 : Nat.count Nat.Prime 19 = 7 := by decide
  have h2 : Nat.Prime 19 := by decide
  have h3 := Nat.nth_count h2
  rwa [h1] at h3

macro "eval_a" : tactic => `(tactic| (
  repeat rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add, add_zero]
  simp only [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
    Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
    Nat.nth_prime_four_eq_eleven, nth_prime_five, nth_prime_six, nth_prime_seven]
  try rfl
))

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 0 := by
  rw [a, if_pos rfl]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
lemma test_a_1 : a 1 = 5 := by
  rw [a, if_neg (by decide)]
  eval_a

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
lemma test_a_2 : a 2 = 15 := by
  rw [a, if_neg (by decide)]
  eval_a

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
lemma test_a_3 : a 3 = 36 := by
  rw [a, if_neg (by decide)]
  eval_a

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
lemma test_a_4 : a 4 = 67 := by
  rw [a, if_neg (by decide)]
  eval_a

/--
Terms are squares at only(?) three values of n = 3, 6, 4072:
corresponding terms are 6^2, 13^2, and 15735^2.
-/
@[category research open, AMS 11]
theorem main_conjecture :
    ∀ n : ℕ, 0 < n → ((∃ m : ℕ, a n = m * m) ↔ (n = 3 ∨ n = 6 ∨ n = 4072)) := by
  sorry

end OeisA105720
