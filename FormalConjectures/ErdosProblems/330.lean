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

/-- `Rep_h A h m` means `m` is a sum of `h` elements of `A`. -/
def Rep_h (A : Set ℕ) (h m : ℕ) : Prop :=
  ∃ f : Fin h → ℕ, (∀ i, f i ∈ A) ∧ (∑ i : Fin h, f i) = m

/-- Integers not representable as a sum of `h` elements of `A` without using `n`. -/
def UnrepWithout (A : Set ℕ) (h n : ℕ) : Set ℕ :=
  {m | ¬ Rep_h (A \ {n}) h m}

/-- “Is an asymptotic add-basis for some order.” -/
def IsAsymptoticAddBasis (A : Set ℕ) : Prop :=
  ∃ h : ℕ, Set.IsAsymptoticAddBasisOfOrder A h

/-- Order-agnostic minimal asymptotic add-basis. -/
def MinAsymptoticAddBasis (A : Set ℕ) : Prop :=
  IsAsymptoticAddBasis A ∧
    ∀ ⦃n⦄, n ∈ A → ¬ IsAsymptoticAddBasis (A \ {n})

@[category research open, AMS 5 11]
theorem erdos_330_statement
    (A : Set ℕ) (h : ℕ)
    (h2   : 2 ≤ h)
    (hmin : MinAsymptoticAddBasis A)
    (hord : Set.IsAsymptoticAddBasisOfOrder A h)
    (hden : Set.HasPosDensity A) :
    ∀ n ∈ A, Set.HasPosDensity (UnrepWithout A h n) ↔ answer(sorry) := by
  sorry

end Erdos330
