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
# Cartesian walk coordinates driven by prime directions

List of $x$-coordinates of prime numbers placed in a 2D Cartesian grid along directions
determined by prime values.

*References:*
- [A379643](https://oeis.org/A379643)
-/
open Nat Finset

namespace OeisA379643

/--
The $x$-coordinate sequence of primes on the 2D Cartesian grid.
-/
noncomputable def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to
  -- $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((range (p_n + 1)).filter (fun p => p.Prime ∧ p % 8 = b)).card

  (count_primes_mod_b 3 : ℤ) - (count_primes_mod_b 7 : ℤ)

@[category API, AMS 11]
lemma nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq ⟨by norm_num, fun x hx => by
    rcases Nat.lt_or_ge x 2 with h|h
    · interval_cases x <;> revert hx <;> decide
    · exact h⟩

@[category API, AMS 11]
lemma nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by
  rw [Nat.nth_eq_sInf Nat.Prime 1]
  exact IsLeast.csInf_eq
    ⟨⟨by norm_num, by intro k hk; interval_cases k; rw [nth_prime_zero]; norm_num⟩,
    fun x ⟨hx_prime, hx_lt⟩ => by
    have h0 := hx_lt 0 (by decide); rw [nth_prime_zero] at h0
    rcases Nat.lt_or_ge x 3 with h|h
    · have : x = 2 := by omega
      subst this; revert h0; norm_num
    · exact h⟩

@[category API, AMS 11]
lemma nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by
  rw [Nat.nth_eq_sInf Nat.Prime 2]
  exact IsLeast.csInf_eq
    ⟨⟨by norm_num,
      by intro k hk; interval_cases k; rw [nth_prime_zero]; norm_num; rw [nth_prime_one]; norm_num⟩,
     fun x ⟨hx_prime, hx_lt⟩ => by
    have h1 := hx_lt 1 (by decide); rw [nth_prime_one] at h1
    rcases Nat.lt_or_ge x 5 with h|h
    · have : x = 4 := by omega
      subst this; norm_num at hx_prime
    · exact h⟩

@[category API, AMS 11]
lemma nth_prime_three : Nat.nth Nat.Prime 3 = 7 := by
  rw [Nat.nth_eq_sInf Nat.Prime 3]
  exact IsLeast.csInf_eq
    ⟨⟨by norm_num,
      by intro k hk; interval_cases k;
         rw [nth_prime_zero]; norm_num;
         rw [nth_prime_one]; norm_num;
         rw [nth_prime_two]; norm_num⟩,
     fun x ⟨hx_prime, hx_lt⟩ => by
    have h2 := hx_lt 2 (by decide); rw [nth_prime_two] at h2
    rcases Nat.lt_or_ge x 7 with h|h
    · have : x = 6 := by omega
      subst this; norm_num at hx_prime
    · exact h⟩

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by unfold a; norm_num

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  unfold a
  have hn : 2 ≠ 0 := by decide
  rw [if_neg hn]
  have h_pn : Nat.nth Nat.Prime (2 - 1) = 3 := nth_prime_one
  rw [h_pn]
  dsimp
  have h3 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 3) (range (3 + 1))).card = 1 :=
    by rfl
  rw [h3]
  have h7 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 7) (range (3 + 1))).card = 0 :=
    by rfl
  rw [h7]
  norm_num

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  unfold a
  have hn : 3 ≠ 0 := by decide
  rw [if_neg hn]
  have h_pn : Nat.nth Nat.Prime (3 - 1) = 5 := nth_prime_two
  rw [h_pn]
  dsimp
  have h3 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 3) (range (5 + 1))).card = 1 :=
    by rfl
  rw [h3]
  have h7 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 7) (range (5 + 1))).card = 0 :=
    by rfl
  rw [h7]
  norm_num

@[category test, AMS 11]
theorem a_4 : a 4 = 0 := by
  unfold a
  have hn : 4 ≠ 0 := by decide
  rw [if_neg hn]
  have h_pn : Nat.nth Nat.Prime (4 - 1) = 7 := nth_prime_three
  rw [h_pn]
  dsimp
  have h3 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 3) (range (7 + 1))).card = 1 :=
    by rfl
  rw [h3]
  have h7 : (Finset.filter (fun p => p.Prime ∧ p % 8 = 7) (range (7 + 1))).card = 1 :=
    by rfl
  rw [h7]
  norm_num

/--
A379731: List of $y$ coordinates of prime numbers in a Cartesian grid.
The sequence term $b(n)$ is given by the formula:
$$b(n) = \pi_{8,5}(p_n) - \pi_{8,1}(p_n)$$
where $p_n$ is the $n$-th prime.
-/
noncomputable def b (n : ℕ) : ℤ :=
  if n = 0 then 0 else
  -- $p_n$ is the $n$-th prime. Nat.nth Nat.Prime is 0-indexed.
  let p_n : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Define $\pi_{8,b}(p_n)$ as the cardinality of the set of primes $\le p_n$ congruent to
  -- $b \pmod 8$.
  let count_primes_mod_b (b : ℕ) : ℕ :=
    ((range (p_n + 1)).filter (fun p => p.Prime ∧ p % 8 = b)).card

  (count_primes_mod_b 5 : ℤ) - (count_primes_mod_b 1 : ℤ)

/-- Conjecture: no prime appears on the negative y-axis.
That is, for every $n \ge 1$, if the $x$-coordinate $a(n)$ is $0$, then the $y$-coordinate $b(n)$
must be non-negative. -/
@[category research open, AMS 11]
theorem not_zero_and_negative : ∀ (n : ℕ), 0 < n → ¬ (a n = 0 ∧ b n < 0) := by sorry

end OeisA379643
