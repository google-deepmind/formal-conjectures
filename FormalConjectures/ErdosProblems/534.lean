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

/-!
# Erdős Problem 534

*Reference:* [erdosproblems.com/534](https://www.erdosproblems.com/534)

What is the largest possible subset $A \subseteq \{1, \ldots, N\}$ containing $N$ such that
$\gcd(a, b) > 1$ for all distinct $a, b \in A$?

A problem of Erdős and Graham [Er73]. They originally conjectured that the
maximum is either $N/p$ (where $p$ is the smallest prime factor of $N$) or the number
of even integers $2t \leq N$ with $\gcd(2t, N) > 1$. Ahlswede and Khachatrian found
a counterexample to this conjecture in 1992.

Erdős then gave a refined conjecture: if $N = q_1^{k_1} \cdots q_r^{k_r}$ where
$q_1 < \cdots < q_r$ are distinct primes, then the maximum is achieved by taking,
for some $1 \leq j \leq r$, all integers in $[1, N]$ divisible by at least one element
of $\{2q_1, \ldots, 2q_j, q_1 \cdots q_j\}$.

This was proved by Ahlswede and Khachatrian [AhKh96].

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138.

[AhKh96] Ahlswede, R. and Khachatrian, L.H., *Sets of integers and quasi-integers with
pairwise common divisor* (1996).
-/

open Finset BigOperators Classical

namespace Erdos534

/-- The set of prime factors of $N$. -/
noncomputable def primeFactors (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ∣ N)

/-- The Erdős–Ahlswede–Khachatrian candidate family: for a set $S$ of primes,
    all $m \in \{1, \ldots, N\}$ divisible by $2p$ for some $p \in S$ or by
    $\prod_{p \in S} p$. -/
noncomputable def candidate (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m =>
    (∃ p ∈ S, (2 * p) ∣ m) ∨ (∏ p ∈ S, p) ∣ m

/--
Erdős Problem 534 [Er73], proved by Ahlswede–Khachatrian [AhKh96]:

If $q_1 < \cdots < q_r$ are the distinct prime factors of $N \geq 2$, then the maximum size
of a subset $A \subseteq \{1, \ldots, N\}$ containing $N$ with $\gcd(a, b) > 1$ for all distinct
$a, b \in A$ is achieved by the candidate family for some initial segment
$\{q_1, \ldots, q_j\}$ of the prime factors.
-/
@[category research solved, AMS 5 11]
theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ S : Finset ℕ, S ⊆ primeFactors N ∧ S.Nonempty ∧
      (∀ p ∈ primeFactors N, ∀ q ∈ S, p ≤ q → p ∈ S) ∧
      N ∈ candidate N S ∧
      (∀ a ∈ candidate N S, ∀ b ∈ candidate N S,
        a ≠ b → 1 < Nat.gcd a b) ∧
      (∀ A : Finset ℕ, A ⊆ Icc 1 N → N ∈ A →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 < Nat.gcd a b) →
        A.card ≤ (candidate N S).card) := by
  sorry

end Erdos534
