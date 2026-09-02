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
# Smallest index $k > n$ such that $(p_k+p_{k+1})/(p_n+p_{n+1})$ is an integer $\ge 2$

*References:*
- [A167918](https://oeis.org/A167918)-/

namespace OeisA167918

/-- $P(i)$ is the $i$-th prime, 1-indexed. -/
noncomputable def P (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- $S(i) = p_i + p_{i+1}$. -/
noncomputable def S (i : ℕ) : ℕ := P i + P (i + 1)

/-- Smallest index $k > n$ such that $S(n) \mid S(k)$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sInf { k : ℕ | k > n ∧ S n ∣ S k }

/-- Value of the sequence `a` at 0. -/
@[category test, AMS 11]
theorem a_0 : a 0 = 0 := by rfl

@[category API, AMS 11]
lemma P_1 : P 1 = 2 := Nat.nth_prime_zero_eq_two

@[category API, AMS 11]
lemma P_2 : P 2 = 3 := Nat.nth_prime_one_eq_three

@[category API, AMS 11]
lemma P_3 : P 3 = 5 := Nat.nth_prime_two_eq_five

@[category API, AMS 11]
lemma P_4 : P 4 = 7 := Nat.nth_prime_three_eq_seven

@[category API, AMS 11]
lemma P_5 : P 5 = 11 := Nat.nth_prime_four_eq_eleven

@[category API, AMS 11]
lemma P_6 : P 6 = 13 := by
  dsimp [P]
  have h : (13 : ℕ).Prime := by decide
  exact Nat.nth_count h

@[category API, AMS 11]
lemma P_7 : P 7 = 17 := by
  dsimp [P]
  have h : (17 : ℕ).Prime := by decide
  exact Nat.nth_count h

@[category API, AMS 11]
lemma P_8 : P 8 = 19 := by
  dsimp [P]
  have h : (19 : ℕ).Prime := by decide
  exact Nat.nth_count h

@[category API, AMS 11]
lemma S_1 : S 1 = 5 := by dsimp [S]; rw [P_1, P_2]

@[category API, AMS 11]
lemma S_2 : S 2 = 8 := by dsimp [S]; rw [P_2, P_3]

@[category API, AMS 11]
lemma S_3 : S 3 = 12 := by dsimp [S]; rw [P_3, P_4]

@[category API, AMS 11]
lemma S_4 : S 4 = 18 := by dsimp [S]; rw [P_4, P_5]

@[category API, AMS 11]
lemma S_5 : S 5 = 24 := by dsimp [S]; rw [P_5, P_6]

@[category API, AMS 11]
lemma S_6 : S 6 = 30 := by dsimp [S]; rw [P_6, P_7]

@[category API, AMS 11]
lemma S_7 : S 7 = 36 := by dsimp [S]; rw [P_7, P_8]

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 6 := by
  have h_least : IsLeast { k : ℕ | k > 1 ∧ S 1 ∣ S k } 6 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      rw [S_1, S_6]
      decide
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_gt := hk.1
      interval_cases k
      · have hdiv := hk.2
        rw [S_1, S_2] at hdiv
        revert hdiv; decide
      · have hdiv := hk.2
        rw [S_1, S_3] at hdiv
        revert hdiv; decide
      · have hdiv := hk.2
        rw [S_1, S_4] at hdiv
        revert hdiv; decide
      · have hdiv := hk.2
        rw [S_1, S_5] at hdiv
        revert hdiv; decide
  have ha1 : a 1 = sInf { k : ℕ | k > 1 ∧ S 1 ∣ S k } := by
    unfold a; split <;> [omega; rfl]
  rw [ha1, h_least.csInf_eq]

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 5 := by
  have h_least : IsLeast { k : ℕ | k > 2 ∧ S 2 ∣ S k } 5 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      rw [S_2, S_5]
      decide
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_gt := hk.1
      interval_cases k
      · have hdiv := hk.2
        rw [S_2, S_3] at hdiv
        revert hdiv; decide
      · have hdiv := hk.2
        rw [S_2, S_4] at hdiv
        revert hdiv; decide
  have ha2 : a 2 = sInf { k : ℕ | k > 2 ∧ S 2 ∣ S k } := by
    unfold a; split <;> [omega; rfl]
  rw [ha2, h_least.csInf_eq]

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 5 := by
  have h_least : IsLeast { k : ℕ | k > 3 ∧ S 3 ∣ S k } 5 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      rw [S_3, S_5]
      decide
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_gt := hk.1
      interval_cases k
      · have hdiv := hk.2
        rw [S_3, S_4] at hdiv
        revert hdiv; decide
  have ha3 : a 3 = sInf { k : ℕ | k > 3 ∧ S 3 ∣ S k } := by
    unfold a; split <;> [omega; rfl]
  rw [ha3, h_least.csInf_eq]

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 7 := by
  have h_least : IsLeast { k : ℕ | k > 4 ∧ S 4 ∣ S k } 7 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      rw [S_4, S_7]
      decide
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_gt := hk.1
      interval_cases k
      · have hdiv := hk.2
        rw [S_4, S_5] at hdiv
        revert hdiv; decide
      · have hdiv := hk.2
        rw [S_4, S_6] at hdiv
        revert hdiv; decide
  have ha4 : a 4 = sInf { k : ℕ | k > 4 ∧ S 4 ∣ S k } := by
    unfold a; split <;> [omega; rfl]
  rw [ha4, h_least.csInf_eq]

/--
Conjecture: $f(n, k) = 2$ for infinitely many cases, where $k = a(n)$.

We assume $a(n) \ne 0$ (i.e., that a suitable $k > n$ always exists), as `sInf` evaluates to $0$
on an empty set.
-/
@[category research open, AMS 11]
theorem conjecture1 (M : ℕ) (ha : ∀ n > 0, a n ≠ 0) :
    ∃ n : ℕ, n ≥ M ∧ n > 0 ∧ S (a n) = 2 * S n := by
  sorry

/--
Open problem: Whether the ratio $f(n, k)$ is bounded, where $k = a(n)$.

We assume $a(n) \ne 0$ (i.e., that a suitable $k > n$ always exists), as `sInf` evaluates to $0$
on an empty set.
-/
@[category research open, AMS 11]
theorem conjecture2 (ha : ∀ n > 0, a n ≠ 0) :
    ∃ C : ℕ, ∀ n : ℕ, n > 0 → S (a n) / S n ≤ C := by
  sorry


end OeisA167918
