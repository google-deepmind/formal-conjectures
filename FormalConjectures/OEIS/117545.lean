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
# Least $k$ such that cyclotomic polynomial $\Phi_k(n)$ is prime

$a(n) = \min \{k \in \mathbb{N} \mid 0 < k \wedge \text{Prime}(|\Phi_k(n)|) \}$,
where $\Phi_k(n)$ is the $k$-th cyclotomic polynomial evaluated at $n$.

*References:*
- [A117545](https://oeis.org/A117545)-/

namespace OeisA117545

/-- Least $k > 0$ such that $|\Phi_k(n)|$ is prime, or $0$ if no such $k$ exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (n : ℤ)).natAbs.Prime}

/-- Value of the sequence `a` at 1. -/
@[category test, AMS 11]
theorem a_1 : a 1 = 2 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (1 :
  ℤ)).natAbs.Prime} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      have : Polynomial.cyclotomic 2 ℤ = Polynomial.X + 1 := Polynomial.cyclotomic_two ℤ
      rw [this]
      norm_num
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_pos := hk.1
      interval_cases k
      have hk2 := hk.2
      have h1 : Polynomial.cyclotomic 1 ℤ = Polynomial.X - 1 := Polynomial.cyclotomic_one ℤ
      rw [h1] at hk2
      revert hk2
      norm_num
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 2. -/
@[category test, AMS 11]
theorem a_2 : a 2 = 2 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (2 :
  ℤ)).natAbs.Prime} 2 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      have : Polynomial.cyclotomic 2 ℤ = Polynomial.X + 1 := Polynomial.cyclotomic_two ℤ
      rw [this]
      norm_num
    · intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      by_contra! h
      have hk_pos := hk.1
      interval_cases k
      have hk2 := hk.2
      have h1 : Polynomial.cyclotomic 1 ℤ = Polynomial.X - 1 := Polynomial.cyclotomic_one ℤ
      rw [h1] at hk2
      revert hk2
      norm_num
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 3. -/
@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (3 :
  ℤ)).natAbs.Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      have h1 : Polynomial.cyclotomic 1 ℤ = Polynomial.X - 1 := Polynomial.cyclotomic_one ℤ
      rw [h1]
      norm_num
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/-- Value of the sequence `a` at 4. -/
@[category test, AMS 11]
theorem a_4 : a 4 = 1 := by
  have h_least : IsLeast {k : ℕ | 0 < k ∧ ((Polynomial.cyclotomic k ℤ).eval (4 :
  ℤ)).natAbs.Prime} 1 := by
    constructor
    · simp only [Set.mem_ofPred_eq]
      refine ⟨by decide, ?_⟩
      have h1 : Polynomial.cyclotomic 1 ℤ = Polynomial.X - 1 := Polynomial.cyclotomic_one ℤ
      rw [h1]
      norm_num
    · intro k hk
      exact hk.1
  exact h_least.csInf_eq

/--
Is $a(n)$ defined for all $n \ge 1$?
That is, for every $n \ge 1$, does there exist $k > 0$ such that $|\Phi_k(n)|$ is prime?-/
@[category research open, AMS 11]
theorem conjecture (n : ℕ) (hn : 0 < n) :
    ∃ k > 0, ((Polynomial.cyclotomic k ℤ).eval (n : ℤ)).natAbs.Prime := by
  sorry

end OeisA117545
