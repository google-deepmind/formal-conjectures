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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 330

*Reference:* [erdosproblems.com/330](https://www.erdosproblems.com/330)
-/

namespace Erdos330

open Set
open scoped BigOperators

/-- `Rep A m` means `m` is a sum of **finitely many** elements of `A`
    (i.e., representable by *some* finite number of terms, not a fixed order). -/
def Rep (A : Set ℕ) (m : ℕ) : Prop :=
  ∃ k : ℕ, ∃ f : Fin k → ℕ, (∀ i, f i ∈ A) ∧ (∑ i : Fin k, f i) = m

/-- Integers **not** representable as a finite sum of elements of `A` **while avoiding** `n`. -/
def UnrepWithout (A : Set ℕ) (n : ℕ) : Set ℕ :=
  {m | ¬ Rep (A \ {n}) m}

/-- An asymptotic additive basis is minimal when one cannot obtain an asymptotic
additive basis by removing any element from it. -/
def MinAsymptoticAddBasis (A : Set ℕ) : Prop :=
  IsAsymptoticAddBasis A ∧ ∀ n ∈ A, ¬ IsAsymptoticAddBasis (A \ {n})
/--
Suppose $A \subset \mathbb{N}$ is a minimal basis with positive density.
Is it true that, for any $n \in A$, the (upper) density of integers which 
cannot be represented without using $n$ is positive?
-/
@[category research open, AMS 5 11]
theorem erdos_330_statement :
    (∀ (A : Set ℕ),  MinAsymptoticAddBasis A → A.HasPosDensity →
    ∀ n ∈ A, Set.HasPosDensity (UnrepWithout A n)) ↔ answer(sorry) := by
  sorry

end Erdos330
