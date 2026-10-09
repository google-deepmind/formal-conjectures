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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 471

*References:*
- [erdosproblems.com/471](https://www.erdosproblems.com/471)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
  number theory*. Monographies de L'Enseignement Mathematique (1980), p. 94.
-/

@[expose] public section

namespace Erdos471

/-- Retain Q and adjoin prime sums of three pairwise distinct members of Q. -/
def step (Q : Finset ℕ) : Finset ℕ :=
  Q ∪ ((((Q.product Q).product Q).filter fun t =>
    t.1.1 ≠ t.1.2 ∧ t.1.1 ≠ t.2 ∧ t.1.2 ≠ t.2 ∧
      Nat.Prime (t.1.1 + t.1.2 + t.2)).image fun t => t.1.1 + t.1.2 + t.2)

/-- The index starts at zero, exactly as in the source. -/
def stage (Q : Finset ℕ) : ℕ → Finset ℕ
  | 0 => Q
  | i + 1 => step (stage Q i)

/--
Given a finite set of primes $Q=Q_0$, define a sequence of sets $Q_i$ by letting
$Q_{i+1}$ be $Q_i$ together with all primes formed by adding three distinct elements of
$Q_i$. Is there some initial choice of $Q$ such that the $Q_i$ become arbitrarily large?

Mrazović and Kovač, and independently Alon, observed that the answer follows from
Vinogradov's theorem that every sufficiently large odd integer is a sum of three distinct
primes. One can start with all primes up to a sufficiently large threshold.
-/
@[category research solved, AMS 11]
theorem erdos_471 : answer(True) ↔
    ∃ Q : Finset ℕ, (∀ p ∈ Q, Nat.Prime p) ∧
      ∀ B : ℕ, ∃ i : ℕ, B < (stage Q i).card := by sorry

/-- In particular, what about $Q=\{3,5,7,11\}$? -/
@[category research open, AMS 11]
theorem erdos_471.variants.ulam_seed : answer(sorry) ↔
    ∀ B : ℕ, ∃ i : ℕ, B < (stage {3, 5, 7, 11} i).card := by sorry

/-- The first stage for Ulam's seed adds $19$ and $23$. -/
@[category test, AMS 11]
theorem ulam_seed_first_stage : stage {3, 5, 7, 11} 1 = {3, 5, 7, 11, 19, 23} := by
  decide

end Erdos471
