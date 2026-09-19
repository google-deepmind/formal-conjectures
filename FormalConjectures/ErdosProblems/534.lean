/-
Copyright 2025 The Formal Conjectures Authors.

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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 534

*References:*
- [erdosproblems.com/534](https://www.erdosproblems.com/534)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117-138.
- [Er80] Erdős, Paul, _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89-115.
- [AhKh96] Ahlswede, Rudolf and Khachatrian, Levon H., _Sets of integers with pairwise common
  divisor and a factor from a specified set of primes_. Acta Arith. (1996), 259--276.
-/

@[expose] public section

namespace Erdos534

/-- A set `A ⊆ {1, …, N}` is *admissible* if it contains `N` and any two distinct elements
of `A` have a common factor. -/
def IsAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ N ∈ A ∧ (A : Set ℕ).Pairwise fun a b ↦ 1 < Nat.gcd a b

/-- The largest size of an admissible subset of `{1, …, N}`. -/
noncomputable def maxCard (N : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℕ, IsAdmissible N A ∧ A.card = n}

/-- The prime factors `q₁ < ⋯ < qⱼ` of `N` which are at most `q`. -/
def primePrefix (N q : ℕ) : Finset ℕ := N.primeFactors.filter (· ≤ q)

/-- The Ahlswede–Khachatrian set associated to a prime factor `q` of `N`: those integers in
`[1, N]` which are a multiple of at least one of `2 q₁, …, 2 qⱼ, q₁ ⋯ qⱼ`, where
`q₁ < ⋯ < qⱼ = q` are the prime factors of `N` which are at most `q`. -/
def ahlswedeKhachatrian (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun m ↦
    (∏ p ∈ primePrefix N q, p) ∣ m ∨ ∃ p ∈ primePrefix N q, 2 * p ∣ m

/--
What is the largest possible subset $A\subseteq\{1,\ldots,N\}$ which contains $N$ such that
$\mathrm{gcd}(a,b)>1$ for all $a\neq b\in A$?

Erdős conjectured that if $N=q_1^{k_1}\cdots q_r^{k_r}$ (where $q_1<\cdots <q_r$ are distinct
primes) then the maximum is achieved by, for some $1\leq j\leq r$, those integers in $[1,N]$
which are a multiple of at least one of $\{2q_1,\ldots,2q_j,q_1\cdots q_j\}$.

This conjecture was proved by Ahlswede and Khachatrian [AhKh96].
-/
@[category research solved, AMS 5 11, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos534.lean#L39"]
theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors, IsAdmissible N (ahlswedeKhachatrian N q) ∧
      maxCard N = (ahlswedeKhachatrian N q).card := by
  sorry

end Erdos534
