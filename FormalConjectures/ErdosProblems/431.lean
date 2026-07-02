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
# Erdős Problem 431

*Reference:* [erdosproblems.com/431](https://www.erdosproblems.com/431)

Are there two infinite sets `A` and `B` of natural numbers such that the sumset
`A + B` agrees with the set of prime numbers up to finitely many exceptions?
-/

noncomputable section

namespace Erdos431

open Classical

/-- A set of natural numbers is infinite in the elementary unbounded sense. -/
def InfiniteSet (A : Set ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n ∈ A

/-- The sumset `A + B`. -/
def Sumset (A B : Set ℕ) (n : ℕ) : Prop :=
  ∃ a b : ℕ, a ∈ A ∧ b ∈ B ∧ a + b = n

/-- Two predicates agree away from finitely many initial exceptions. -/
def AgreeUpToFinitelyManyExceptions (P Q : ℕ → Prop) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (P n ↔ Q n)

/-- The inverse Goldbach question of Ostmann. -/
def Erdos431Question : Prop :=
  ∃ A B : Set ℕ,
    InfiniteSet A ∧
      InfiniteSet B ∧
        AgreeUpToFinitelyManyExceptions (Sumset A B) Nat.Prime

/-- Can the primes be equal, up to finitely many exceptions, to `A + B`? -/
@[category research open, AMS 11]
theorem erdos_431 : answer(sorry) ↔ Erdos431Question := by
  sorry

end Erdos431

end
