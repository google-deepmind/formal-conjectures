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
# Representations of $2n$ as $p + p' + q + q'$

$a(n)$ is the number of ways to write $2n$ as $p + p' + q + q'$, where $p \le q$ are primes,
and $r'$ denotes the smallest prime strictly greater than $r$.

*References:*
- [A389790](https://oeis.org/A389790)
-/

open Nat Finset

namespace OeisA389790

/-- The smallest prime strictly greater than $r$. Defined non-computably using the set infimum. -/
noncomputable def next_prime (r : ℕ) : ℕ :=
  sInf {k : ℕ | k.Prime ∧ r < k}

/-- $r + r'$, where $r'$ is the next prime after $r$. -/
noncomputable def S_sum (r : ℕ) : ℕ := r + next_prime r

/--
Number of ways to write $2n$ as $p + p' + q + q'$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let target := 2 * n
  let R := range n
  ((R ×ˢ R).filter (fun ⟨p, q⟩ =>
    p.Prime ∧ q.Prime ∧ p ≤ q ∧ S_sum p + S_sum q = target
  )).card

@[category API, AMS 11]
lemma next_prime_2 : next_prime 2 = 3 := by
  unfold next_prime
  refine IsLeast.csInf_eq ⟨⟨by decide, by decide⟩, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 3 with h|h
  · interval_cases k
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
  · exact h

@[category API, AMS 11]
lemma next_prime_3 : next_prime 3 = 5 := by
  unfold next_prime
  refine IsLeast.csInf_eq ⟨⟨by decide, by decide⟩, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k 5 with h|h
  · interval_cases k
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
    · exfalso; revert hk; decide
  · exact h

@[category API, AMS 11]
lemma S_sum_2 : S_sum 2 = 5 := by unfold S_sum; rw [next_prime_2]
@[category API, AMS 11]
lemma S_sum_3 : S_sum 3 = 8 := by unfold S_sum; rw [next_prime_3]

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 0 := by rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 0 := by
  unfold a
  apply Finset.card_eq_zero.mpr
  ext ⟨p, q⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨hp_lt, hq_lt⟩, hp_prime, hq_prime, hp_le_q, h_eq⟩
    interval_cases p
    · exfalso; revert hp_prime; decide
    · exfalso; revert hp_prime; decide
    · interval_cases q
      rw [S_sum_2] at h_eq
      exfalso; revert h_eq; decide
  · intro h; exfalso; simp_all

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  apply Finset.card_eq_zero.mpr
  ext ⟨p, q⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨hp_lt, hq_lt⟩, hp_prime, hq_prime, hp_le_q, h_eq⟩
    interval_cases p
    · exfalso; revert hp_prime; decide
    · exfalso; revert hp_prime; decide
    · interval_cases q
      · rw [S_sum_2] at h_eq
        exfalso; revert h_eq; decide
      · rw [S_sum_2, S_sum_3] at h_eq
        exfalso; revert h_eq; decide
    · interval_cases q
      rw [S_sum_3] at h_eq
      exfalso; revert h_eq; decide
  · intro h; exfalso; simp_all

/--
Conjecture 1: $a(n) > 0$ for all $n \ge 474$.
This is an analog of Goldbach's conjecture.
-/
@[category research open, AMS 11]
theorem conjecture_1 : ∀ n : ℕ, 474 ≤ n → 0 < a n := by
  sorry

/--
Conjecture 2: For all $k$, there exists $n_k$ such that $a(m) > k$ for all $m \ge n_k$.
-/
@[category research open, AMS 11]
theorem conjecture_2 : ∀ k : ℕ, ∃ n_k : ℕ, ∀ m : ℕ, n_k ≤ m → k < a m := by
  sorry

/-- The statement that $n_{max}$ is the conjectured largest value of $n$ such that $a(n) = k$. -/
def is_conjectured_largest_value (n_max k : ℕ) : Prop :=
  a n_max = k ∧ ∀ n > n_max, a n ≠ k

/--
Conjecture 3: $a(n) = k$ for a largest value of $n$ given by the table:
$k=2 \implies 833$, $k=3 \implies 1487$, $k=4 \implies 1411$, $k=5 \implies 1523$,
$k=6 \implies 1747$, $k=7 \implies 2621$, $k=8 \implies 2153$, $k=9 \implies 3091$,
$k=10 \implies 3238$.
-/
@[category research open, AMS 11]
theorem conjecture_3 :
    is_conjectured_largest_value 833 2 ∧
    is_conjectured_largest_value 1487 3 ∧
    is_conjectured_largest_value 1411 4 ∧
    is_conjectured_largest_value 1523 5 ∧
    is_conjectured_largest_value 1747 6 ∧
    is_conjectured_largest_value 2621 7 ∧
    is_conjectured_largest_value 2153 8 ∧
    is_conjectured_largest_value 3091 9 ∧
    is_conjectured_largest_value 3238 10 := by
  sorry

end OeisA389790
