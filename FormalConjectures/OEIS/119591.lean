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
# Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime

$a(n) = \min \{k \ge 1 \mid \text{Prime}(2 \cdot n^k - 1)\}$ for $n \ge 2$.

*References:*
- [A119591](https://oeis.org/A119591)-/

namespace OeisA119591

/-- Least $k \ge 1$ such that $2 \cdot n^k - 1$ is prime, or $0$ if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (2 * n ^ k - 1).Prime}

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by
  dsimp [a]
  have h_empty : {k : ℕ | 0 < k ∧ (2 * 0 ^ k - 1).Prime} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hk
    rw [zero_pow hk.ne', mul_zero, show (0 - 1 : ℕ) = 0 from rfl]
    exact Nat.not_prime_zero
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 0 := by
  dsimp [a]
  have h_empty : {k : ℕ | 0 < k ∧ (2 * 1 ^ k - 1).Prime} = ∅ := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    rw [one_pow, mul_one, show (2 - 1 : ℕ) = 1 from rfl]
    exact Nat.not_prime_one
  rw [h_empty, Nat.sInf_empty]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 2 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 3 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 4 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 5. -/
@[category test, AMS 11]
theorem a_5 : a 5 = 4 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 5 ^ k - 1).Prime} 4 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_pos := hk.1
      interval_cases k
      · have hk2 := hk.2
        revert hk2
        norm_num
      · have hk2 := hk.2
        revert hk2
        norm_num
      · have hk2 := hk.2
        revert hk2
        norm_num
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 6. -/
@[category test, AMS 11]
theorem a_6 : a 6 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ (2 * 6 ^ k - 1).Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, by norm_num⟩
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/--
Is $a(n)$ defined for all $n \ge 2$?
That is, does there exist $k > 0$ such that $2 \cdot n^k - 1$ is prime?-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 2 ≤ n) : ∃ k > 0, (2 * n ^ k - 1).Prime := by
  sorry

end OeisA119591
