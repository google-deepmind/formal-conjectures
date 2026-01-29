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

/-- `Rep A m h` means `m` is a sum of at most `h` elements of `A`x. -/
def Rep (A : Set ℕ) (m h : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ h ∧ ∃ f : Fin k → ℕ, (∀ i, f i ∈ A) ∧ (∑ i : Fin k, f i) = m

/-- Integers **not** representable as a finite sum of elements with at most `h` terms of `A`
**while avoiding** `n`. -/
def UnrepWithout (A : Set ℕ) (n h: ℕ) : Set ℕ :=
  {m | ¬ Rep (A \ {n}) m h}

/-- An asymptotic additive basis of order `h` is minimal when one cannot obtain an asymptotic
additive basis by removing any element from it. -/
def MinAsymptoticAddBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticAddBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticAddBasisOfOrder (A \ {n}) h

/--
Does there exist a minimal basis $A \subset \mathbb{N}$ with positive density
such that, for any $n \in A$, the (upper) density of integers which
cannot be represented without using $n$ is positive?
-/
@[category research open, AMS 5 11]
theorem erdos_330_statement :
    answer(sorry) ↔ ∃ (A : Set ℕ), ∃ h, MinAsymptoticAddBasisOfOrder A h ∧ A.HasPosDensity ∧
    ∀ n ∈ A, Set.HasPosDensity (UnrepWithout A n h) := by
  sorry

end Erdos330
