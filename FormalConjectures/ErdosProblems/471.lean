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
# Erdős Problem 471

*Reference:* [erdosproblems.com/471](https://www.erdosproblems.com/471)

Given a finite set of primes $Q = Q_0$, define a sequence of sets $Q_i$ by letting
$Q_{i+1}$ be $Q_i$ together with all primes formed by adding three distinct elements
of $Q_i$. Is there some initial choice of $Q$ such that the $Q_i$ become arbitrarily large?

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathematique **28**,
Université de Genève (1980), p. 94.
-/

namespace Erdos471

/-- Given a set $Q$ of natural numbers, `step Q` is $Q$ together with all
    primes that equal the sum of three distinct elements of $Q$. -/
def step (Q : Set ℕ) : Set ℕ :=
  Q ∪ {p | Nat.Prime p ∧ ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p = a + b + c}

/-- The sequence $Q_i$ starting from $Q_0$. -/
def seq (Q₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => Q₀
  | i + 1 => step (seq Q₀ i)

/--
Erdős Problem 471 (Proved):

Given a finite set of primes $Q = Q_0$, define a sequence of sets $Q_i$ by letting
$Q_{i+1}$ be $Q_i$ together with all primes formed by adding three distinct elements
of $Q_i$. Is there some initial choice of $Q$ such that the $Q_i$ become arbitrarily large?

A problem of Ulam. Proved by Mrazović and Kovač, and independently Alon, using
Vinogradov's theorem that every large odd integer is the sum of three distinct primes.
In particular, there exists $N$ such that every prime $> N$ is the sum of three distinct
smaller primes. Taking $Q_0$ to be all primes $\leq N$, all primes eventually appear.
-/
@[category research solved, AMS 11]
theorem erdos_471 : answer(True) ↔
    ∃ Q₀ : Set ℕ, Q₀.Finite ∧ (∀ p ∈ Q₀, Nat.Prime p) ∧
      ∀ p : ℕ, Nat.Prime p → ∃ i : ℕ, p ∈ seq Q₀ i := by
  sorry

/--
Variant of Erdős Problem 471:

Does the initial set $Q_0 = \{3, 5, 7, 11\}$ suffice? That is, does every prime
eventually appear in the sequence $Q_i$ starting from $\{3, 5, 7, 11\}$?
-/
@[category research open, AMS 11]
theorem erdos_471_variant :
    ∀ p : ℕ, Nat.Prime p → ∃ i : ℕ, p ∈ seq {3, 5, 7, 11} i := by
  sorry

end Erdos471
