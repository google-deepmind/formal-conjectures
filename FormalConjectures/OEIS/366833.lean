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
# Multiplicities in prime-counting sequence A362965

$a(n)$ is the number of times $n$ appears in the sequence A362965 (the number of primes $\le$
the $n$-th prime power).

*References:*
- [A366833](https://oeis.org/A366833)
-/
open Nat

namespace OeisA366833

/--
Number of times $n$ appears in A362965.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- p_n (1-indexed) is Nat.nth Nat.Prime (n-1) (0-indexed). Since n > 0, n-1 is safe.
    let p_n   : ℕ := Nat.nth Nat.Prime (n - 1)
    -- p_{n+1} is Nat.nth Nat.Prime n
    let p_np1 : ℕ := Nat.nth Nat.Prime n

    -- Count the number of prime powers in the inclusive interval [p_n, p_{n+1}]
    let count_prime_powers : ℕ :=
      Finset.card ((Finset.Icc p_n p_np1).filter IsPrimePow)

    -- Subtracting 1 is safe since both p_n and p_{n+1} are prime powers, giving a count >= 2.
    count_prime_powers - 1

@[category API, AMS 11]
lemma prime_0 : Nat.nth Nat.Prime 0 = 2 := by
  rw [Nat.nth_zero]
  exact IsLeast.csInf_eq (s := setOf Nat.Prime) ⟨Nat.prime_two, fun x hx => by
    rcases Nat.lt_or_ge x 2 with h | h
    · interval_cases x
      · exact (Nat.not_prime_zero hx).elim
      · exact (Nat.not_prime_one hx).elim
    · exact h⟩

@[category API, AMS 11]
lemma prime_1 : Nat.nth Nat.Prime 1 = 3 := by
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | x.Prime ∧ ∀ k < 1, Nat.nth Nat.Prime k < x}) ⟨
    ⟨Nat.prime_three, by
      intro k hk
      interval_cases k
      rw [prime_0]
      decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 0 (by decide)
      rw [prime_0] at h0
      exact h0
  ⟩

@[category API, AMS 11]
lemma prime_2 : Nat.nth Nat.Prime 2 = 5 := by
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | x.Prime ∧ ∀ k < 2, Nat.nth Nat.Prime k < x}) ⟨
    ⟨by norm_num, by
      intro k hk
      interval_cases k
      · rw [prime_0]; decide
      · rw [prime_1]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 1 (by decide)
      rw [prime_1] at h0
      have : x ≠ 4 := by
        rintro rfl
        revert hx_cond
        norm_num
      omega
  ⟩

@[category API, AMS 11]
lemma prime_3 : Nat.nth Nat.Prime 3 = 7 := by
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | x.Prime ∧ ∀ k < 3, Nat.nth Nat.Prime k < x}) ⟨
    ⟨by norm_num, by
      intro k hk
      interval_cases k
      · rw [prime_0]; decide
      · rw [prime_1]; decide
      · rw [prime_2]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 2 (by decide)
      rw [prime_2] at h0
      have : x ≠ 6 := by
        rintro rfl
        revert hx_cond
        norm_num
      omega
  ⟩

@[category API, AMS 11]
lemma prime_4 : Nat.nth Nat.Prime 4 = 11 := by
  rw [Nat.nth_eq_sInf]
  exact IsLeast.csInf_eq (s := {x | x.Prime ∧ ∀ k < 4, Nat.nth Nat.Prime k < x}) ⟨
    ⟨by norm_num, by
      intro k hk
      interval_cases k
      · rw [prime_0]; decide
      · rw [prime_1]; decide
      · rw [prime_2]; decide
      · rw [prime_3]; decide⟩,
    fun x ⟨hx_cond, hx_lt⟩ => by
      have h0 := hx_lt 3 (by decide)
      rw [prime_3] at h0
      have : x ≠ 8 ∧ x ≠ 9 ∧ x ≠ 10 := by
        refine ⟨?_, ?_, ?_⟩
        · rintro rfl; revert hx_cond; norm_num
        · rintro rfl; revert hx_cond; norm_num
        · rintro rfl; revert hx_cond; norm_num
      omega
  ⟩

@[category API, AMS 11]
lemma filter_Icc_2_3 : (Finset.Icc 2 3).filter IsPrimePow = {2, 3} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    interval_cases x
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨2, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨3, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩

@[category API, AMS 11]
lemma filter_Icc_3_5 : (Finset.Icc 3 5).filter IsPrimePow = {3, 4, 5} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    interval_cases x
    · left; rfl
    · right; left; rfl
    · right; right; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨3, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨2, 2, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨5, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩

@[category API, AMS 11]
lemma filter_Icc_5_7 : (Finset.Icc 5 7).filter IsPrimePow = {5, 7} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    interval_cases x
    · left; rfl
    · exact False.elim ((by decide : ¬ IsPrimePow 6) h3)
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨5, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨7, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩

@[category API, AMS 11]
lemma filter_Icc_7_11 : (Finset.Icc 7 11).filter IsPrimePow = {7, 8, 9, 11} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    interval_cases x
    · left; rfl
    · right; left; rfl
    · right; right; left; rfl
    · exact False.elim ((by decide : ¬ IsPrimePow 10) h3)
    · right; right; right; rfl
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨7, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨2, 3, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨3, 2, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩
    · exact ⟨⟨by norm_num, by norm_num⟩,
        ⟨11, 1, Nat.prime_iff.mp (by norm_num), by norm_num, by norm_num⟩⟩

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  unfold a
  dsimp
  rw [prime_0, prime_1]
  rw [filter_Icc_2_3]
  rfl

@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  unfold a
  dsimp
  rw [prime_1, prime_2]
  rw [filter_Icc_3_5]
  rfl

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  unfold a
  dsimp
  rw [prime_2, prime_3]
  rw [filter_Icc_5_7]
  rfl

@[category test, AMS 11]
theorem a_4 : a 4 = 3 := by
  unfold a
  dsimp
  rw [prime_3, prime_4]
  rw [filter_Icc_7_11]
  rfl

/--
Conjecture: a(n) can be only 1, 2, or 3 (with the first occurrences of 3 appearing at n = 4, 9,
30, 327 and 3512).
-/
@[category research open, AMS 11]
theorem values_in_one_two_three : ∀ (n : ℕ), 1 ≤ n → a n ∈ ({1, 2, 3} : Finset ℕ) := by
  sorry

end OeisA366833
