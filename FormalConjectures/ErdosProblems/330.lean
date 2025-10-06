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

open Filter Set
open scoped BigOperators

/-- `Rep_h A h m` means `m` is a sum of `h` elements of `A`. -/
def Rep_h (A : Set ℕ) (h m : ℕ) : Prop :=
  ∃ (f : Fin h → ℕ), (∀ i, f i ∈ A) ∧ (∑ i, f i) = m

/-- Integers not representable as a sum of `h` elements of `A` **without** using `n`. -/
def UnrepWithout (A : Set ℕ) (h n : ℕ) : Set ℕ :=
  {m | ¬ Rep_h (A \ {n}) h m}

/-- Minimality built on top of the library predicate `Set.IsAsymptoticAddBasis`. -/
def MinAsymptoticAddBasis (A : Set ℕ) (h : ℕ) : Prop :=
  Set.IsAsymptoticAddBasis A h ∧
    ∀ n ∈ A, ¬ Set.IsAsymptoticAddBasis (A \ {n}) h

/-- **Erdős Problem 330 (informal).**
Suppose `A ⊂ ℕ` is a *minimal* asymptotic add-basis of order `h ≥ 2` with positive (upper) density.
Then for every `n ∈ A`, the set of integers that are **not** representable as a sum of `h` elements
of `A` while avoiding `n` has positive (upper) density. -/
@[category research open, AMS 5 11]
theorem erdos_330_answer :
    ∀ (h : ℕ) (A : Set ℕ),
      2 ≤ h →
      MinAsymptoticAddBasis A h →
      A.HasPosDensity →
      (∀ n ∈ A, (UnrepWithout A h n).HasPosDensity)
      ↔ answer(sorry) := by
  sorry
end Erdos330
