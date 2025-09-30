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
import Mathlib.Data.Nat.Basic

/-!
# Erdős Problem 330

*Reference:* [erdosproblems.com/330](https://www.erdosproblems.com/330)
-/

namespace Erdos330

open Filter Set
open scoped BigOperators

def Rep_h (A : Set ℕ) (h m : ℕ) : Prop :=
  ∃ (f : Fin h → ℕ), (∀ i, f i ∈ A) ∧ (∑ i, f i) = m

def IsAsymptoticBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, ∃ (f : Fin h → ℕ), (∀ i, f i ∈ A) ∧ (∑ i, f i) = m

def MinAsymptoticBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticBasisOfOrder (A \ {n}) h

def UnrepWithout (A : Set ℕ) (h n : ℕ) : Set ℕ :=
  {m | ¬ Rep_h (A \ {n}) h m}

@[category research open, AMS 5]
theorem erdos_330_answer :
    ∀ (h : ℕ) (A : Set ℕ),
      2 ≤ h →
      MinAsymptoticBasisOfOrder A h →
      A.HasPosDensity →
      (∀ n ∈ A, (UnrepWithout A h n).HasPosDensity) := by
  sorry

end Erdos330
