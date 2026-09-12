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
# Smallest prime $p$ such that $p + n$ is an $n$-th power

Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such number exists.
That is, the smallest prime of the form $k^n - n$.

*References:*
- [A084046](https://oeis.org/A084046)-/

namespace OeisA84046

/-- Smallest prime $p$ such that $p + n$ is an $n$-th power, or $0$ if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ n = p + n}

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  change sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 0 = p + 0} = 0
  have h_empty : {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 0 = p + 0} = ∅ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hp ⟨k, hk⟩
    rw [pow_zero, add_zero] at hk
    subst hk
    exact Nat.not_prime_one hp
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 1 = p + 1} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨Nat.prime_two, 3, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      exact hp.1.two_le
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 2 = p + 2} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨Nat.prime_two, 2, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      exact hp.1.two_le
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  have h_least : IsLeast {p : ℕ | p.Prime ∧ ∃ k : ℕ, k ^ 3 = p + 3} 5 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by norm_num, 2, by norm_num⟩
    · intro p hp
      simp only [Set.mem_ofPred_eq] at hp
      rcases hp with ⟨hp_prime, k, hk⟩
      by_contra! h
      interval_cases p
      · exact Nat.not_prime_zero hp_prime
      · exact Nat.not_prime_one hp_prime
      · rcases (show k ≤ 1 ∨ 2 ≤ k by omega) with hk_le | hk_ge
        · interval_cases k <;> revert hk <;> decide
        · have : 8 ≤ k ^ 3 := by
            calc 8 = 2 ^ 3 := by decide
            _ ≤ k ^ 3 := Nat.pow_le_pow_left hk_ge 3
          omega
      · rcases (show k ≤ 1 ∨ 2 ≤ k by omega) with hk_le | hk_ge
        · interval_cases k <;> revert hk <;> decide
        · have : 8 ≤ k ^ 3 := by
            calc 8 = 2 ^ 3 := by decide
            _ ≤ k ^ 3 := Nat.pow_le_pow_left hk_ge 3
          omega
      · exact (by decide : ¬ Nat.Prime 4) hp_prime
  exact h_least.csInf_eq

/--
Conjecture: if a(k) = 0 then k is an even square.-/
@[category research open, AMS 11]
theorem conjecture (k : ℕ) (h : a k = 0) : ∃ m : ℕ, k = (2 * m) ^ 2 := by
  sorry

end OeisA84046
