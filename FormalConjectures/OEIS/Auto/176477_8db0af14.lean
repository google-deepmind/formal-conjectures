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

import FormalConjectures.Util.ProblemImports

open Nat

/-- Helper function for the recurrence relation, defined over $\mathbb{Q}$. -/
noncomputable def a_Q (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  | 1 => 2
  | k + 2 => -- Index $n = k+2$, $n \ge 2$
    let n_idx := k + 2
    let n_q : ℚ := n_idx
    -- The subtraction n_idx - 1 is safe since n_idx ≥ 2
    let a_prev : ℚ := a_Q (n_idx - 1)

    -- Numerator Term 1: $32n^3 a(n-1)$
    let term1 : ℚ := 32 * n_q ^ 3 * a_prev

    -- Polynomial coefficient Term 2
    let P_n : ℚ := 21 * n_q ^ 3 + 22 * n_q ^ 2 + 8 * n_q + 1

    -- Binomial Term 2: $\binom{2n-1}{n}^4$. Subtraction is safe since $2n-1 \ge 3$
    let binom_pow4 : ℚ := (Nat.choose (2 * n_idx - 1) n_idx : ℚ) ^ 4

    let numerator : ℚ := term1 + P_n * binom_pow4
    let denominator : ℚ := (2 * n_q + 1) ^ 3

    numerator / denominator

/--
A176477: $a(1)=2$; for $n \ge 2$,
$$(2n+1)^3 a(n) = 32n^3 a(n-1) + (21n^3 + 22n^2 + 8n + 1) \binom{2n-1}{n}^4.$$
The sequence terms are non-negative integers. We compute the result using the rational recurrence and cast the result to $\mathbb{N}$.
-/
noncomputable def a (n : ℕ) : ℕ := (a_Q n).floor.toNat


theorem a_one : a 1 = 2 := by
  simp only [a, a_Q]
  norm_cast

theorem a_two : a 2 = 181 := by
  sorry

/--
Conjecture of Zhi-Wei Sun (A176477):
Each term $a(n)$ is a positive integer.
Also, $a(n)$ is odd if and only if $n = 2^m$ for some $m \in \mathbb{Z}_{>0}$.
-/
theorem oeis_a176477_conjecture (n : ℕ) (hn : n ≥ 1) :
  a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  sorry
