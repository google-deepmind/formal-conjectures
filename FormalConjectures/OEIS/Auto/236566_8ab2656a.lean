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

open Nat Finset

/--
A236566: Number of ordered ways to write $2n = p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Here $\operatorname{prime}(k)$ denotes the $k$-th prime number $p_k$.
Transcribing this to Mathlib's 0-indexed $p'_{k} = \operatorname{Nat.nth\ Nat.Prime}\ k$, we use $\operatorname{Nat.nth\ Nat.Prime}\ (p+1)$ for $\operatorname{prime}(p + 2)$.
-/
noncomputable def A236566 (n : ℕ) : ℕ :=
  Finset.card <| (Finset.range (2 * n)).filter fun p =>
    Nat.Prime p ∧
    Nat.Prime (2 * n - p) ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2)


theorem a_one : A236566 1 = 0 := by sorry
theorem a_two : A236566 2 = 0 := by sorry
theorem a_three : A236566 3 = 1 := by sorry
theorem a_four : A236566 4 = 2 := by sorry

/-- Twin Prime Conjecture: There are infinitely many primes $p$ such that $p + 2$ is prime. -/
def twin_prime_conjecture : Prop := Set.Infinite {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

/-- Lemoine's Conjecture (or Levy's conjecture): Every odd number $k > 5$ can be written as $p + 2q$, where $p$ and $q$ are prime numbers. -/
def lemoine_conjecture : Prop :=
  ∀ k : ℕ, Odd k → 5 < k → ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ k = p + 2 * q

/--
Conjecture A236566 part (ii):
If $n > 30$, then $2n + 1$ can be written as $2p + q$ with $p, q$ and $\operatorname{prime}(p + 2) + 2$ all prime.
Note: We interpret $\operatorname{prime}(p + 2)$ as $\operatorname{Nat.nth\ Nat.Prime}\ (p + 1)$, following the setup of A236566's Lean definition above,
where $p$ is one of the primes involved in the sum $2n+1 = 2p+q$.
-/
def a236566_conjecture_part_ii : Prop :=
  ∀ n : ℕ, 30 < n → ∃ (p q : ℕ),
    Nat.Prime p ∧
    Nat.Prime q ∧
    Nat.Prime (Nat.nth Nat.Prime (p + 1) + 2) ∧
    2 * n + 1 = 2 * p + q

/--
A236566: Conjecture: Part (ii) implies both Lemoine's conjecture (cf. A046927) and the twin prime conjecture.
-/
theorem oeis_236566_conjecture_2 :
  a236566_conjecture_part_ii → lemoine_conjecture ∧ twin_prime_conjecture := by
  sorry
