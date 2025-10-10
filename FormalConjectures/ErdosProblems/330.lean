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

open scoped BigOperators

/-- `Rep_h A h m` means `m` is a sum of `h` elements of `A`. -/
def Rep_h (A : _root_.Set ℕ) (h m : ℕ) : Prop :=
  ∃ f : Fin h → ℕ, (∀ i, f i ∈ A) ∧ (∑ i : Fin h, f i) = m

/-- Integers not representable as a sum of `h` elements of `A` without using `n`. -/
def UnrepWithout (A : _root_.Set ℕ) (h n : ℕ) : _root_.Set ℕ :=
  {m | ¬ Rep_h (A \ {n}) h m}

/-- Minimality using `_root_.Set.IsAsymptoticAddBasis`. -/
def MinAsymptoticAddBasis (A : _root_.Set ℕ) (h : ℕ) : Prop :=
  _root_.Set.IsAsymptoticAddBasis A h ∧
    ∀ ⦃n⦄, n ∈ A → ¬ _root_.Set.IsAsymptoticAddBasis (A \ {n}) h

@[category research open, AMS 5 11]
theorem erdos_330_statement
    (h : ℕ) (A : _root_.Set ℕ)
    (h2 : 2 ≤ h)
    (hmin : MinAsymptoticAddBasis A h)
    (hden : _root_.Set.HasPosDensity A) :
    ∀ n ∈ A, _root_.Set.HasPosDensity (UnrepWithout A h n) := by
  sorry

end Erdos330
