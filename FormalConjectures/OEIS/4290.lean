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
# Least positive multiple of $n$ in base 10 with digits 0 and 1

Least positive multiple of $n$ that when written in base 10 uses only 0's and 1's.

*References:*
- [A004290](https://oeis.org/A004290)
-/

namespace OeisA4290

/-- Least positive multiple of $n$ using only 0's and 1's in base 10. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 }

@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  dsimp [a]
  have h_empty : { m : ℕ | 0 < m ∧ 0 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } = ∅ := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hm h0dvd
    have hm0 : m = 0 := Nat.eq_zero_of_zero_dvd h0dvd
    omega
  rw [h_empty, Nat.sInf_empty]

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 1 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } 1 := by
    refine ⟨⟨by decide, dvd_rfl, ?_⟩, fun m hm ↦ hm.1⟩
    intro d hd
    rw [Nat.digits_def' (by decide) (by decide), show (1 / 10 : ℕ) = 0 by rfl,
      Nat.digits_zero] at hd
    simp only [show 1 % 10 = 1 by rfl, List.mem_singleton] at hd
    subst hd
    exact Or.inr rfl
  exact h_least.csInf_eq

@[category test, AMS 11]
theorem a_2 : a 2 = 10 := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 2 ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } 10 := by
    refine ⟨⟨by decide, by decide, ?_⟩, ?_⟩
    · intro d hd
      have h10 : (10 : ℕ) = 10 ^ 1 * 1 := by rfl
      nth_rw 2 [h10] at hd
      rw [Nat.digits_base_pow_mul (b := 10) (k := 1) (m := 1) (by decide) (by decide),
          Nat.digits_of_lt 10 1 (by decide) (by decide)] at hd
      simp only [List.replicate_one, List.singleton_append, List.mem_cons,
        List.not_mem_nil, or_false] at hd
      exact hd
    · intro m hm
      by_contra! hlt
      have hm_pos : 0 < m := hm.1
      have h2dvd : 2 ∣ m := hm.2.1
      have hd : ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := hm.2.2
      interval_cases m
      · revert h2dvd; decide
      · have hm_d : Nat.digits 10 2 = [2] := Nat.digits_of_lt 10 2 (by decide) (by decide)
        have h_mem : 2 ∈ Nat.digits 10 2 := by rw [hm_d]; exact List.Mem.head []
        have := hd 2 h_mem; omega
      · have hm_d : Nat.digits 10 3 = [3] := Nat.digits_of_lt 10 3 (by decide) (by decide)
        have h_mem : 3 ∈ Nat.digits 10 3 := by rw [hm_d]; exact List.Mem.head []
        have := hd 3 h_mem; omega
      · have hm_d : Nat.digits 10 4 = [4] := Nat.digits_of_lt 10 4 (by decide) (by decide)
        have h_mem : 4 ∈ Nat.digits 10 4 := by rw [hm_d]; exact List.Mem.head []
        have := hd 4 h_mem; omega
      · have hm_d : Nat.digits 10 5 = [5] := Nat.digits_of_lt 10 5 (by decide) (by decide)
        have h_mem : 5 ∈ Nat.digits 10 5 := by rw [hm_d]; exact List.Mem.head []
        have := hd 5 h_mem; omega
      · have hm_d : Nat.digits 10 6 = [6] := Nat.digits_of_lt 10 6 (by decide) (by decide)
        have h_mem : 6 ∈ Nat.digits 10 6 := by rw [hm_d]; exact List.Mem.head []
        have := hd 6 h_mem; omega
      · have hm_d : Nat.digits 10 7 = [7] := Nat.digits_of_lt 10 7 (by decide) (by decide)
        have h_mem : 7 ∈ Nat.digits 10 7 := by rw [hm_d]; exact List.Mem.head []
        have := hd 7 h_mem; omega
      · have hm_d : Nat.digits 10 8 = [8] := Nat.digits_of_lt 10 8 (by decide) (by decide)
        have h_mem : 8 ∈ Nat.digits 10 8 := by rw [hm_d]; exact List.Mem.head []
        have := hd 8 h_mem; omega
      · have hm_d : Nat.digits 10 9 = [9] := Nat.digits_of_lt 10 9 (by decide) (by decide)
        have h_mem : 9 ∈ Nat.digits 10 9 := by rw [hm_d]; exact List.Mem.head []
        have := hd 9 h_mem; omega
  exact h_least.csInf_eq

/-- $a(10^k) = 10^k$ for all $k$. -/
@[category textbook, AMS 11]
theorem a_ten_pow (k : ℕ) : a (10 ^ k) = 10 ^ k := by
  dsimp [a]
  have h_least : IsLeast { m : ℕ | 0 < m ∧ 10 ^ k ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } (10 ^ k) := by
    refine ⟨⟨Nat.pow_pos (by decide), dvd_rfl, ?_⟩, fun m hm ↦ Nat.le_of_dvd hm.1 hm.2.1⟩
    intro d hd
    have h10k : 10 ^ k = 10 ^ k * 1 := by rw [mul_one]
    rw [h10k, Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by decide) (by decide),
        Nat.digits_of_lt 10 1 (by decide) (by decide)] at hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with ⟨-, rfl⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact h_least.csInf_eq

/--
It is known that $a(10^k - 1) = (10^{9k} - 1) / 9$ for all $k$.
Is $a(n) < a(10^k - 1)$ for all $n < 10^k - 1$?
- David Radcliffe, Aug 01 2025
-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) :
    ∀ n < 10 ^ k - 1, a n < a (10 ^ k - 1) := by
  sorry

end OeisA4290
