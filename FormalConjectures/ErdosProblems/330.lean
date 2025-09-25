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

/-- `Rep_h A m` means `m` is a sum of exactly `h` terms from `A`. -/
def Rep_h (A : Set ℕ) (h m : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ a ∈ s, a ∈ A) ∧ s.card = h ∧ s.sum = m

/-- `A` is an asymptotic additive basis of order `h`. -/
def IsAsymptoticBasisOfOrder (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ᶠ m in atTop, Rep_h A h m

/-- `Basis A h` means `A` is a minimal asymptotic basis of order `h`. -/
def Basis (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticBasisOfOrder A h ∧ ∀ n ∈ A, ¬ IsAsymptoticBasisOfOrder (A \ {n}) h

/-- Integers not representable without using `n` (i.e. by `A \ {n}`) with exactly `h` terms. -/
def UnrepWithout (A : Set ℕ) (h n : ℕ) : Set ℕ := {m | ¬ Rep_h (A \ {n}) h m}

/--
**Erdős 330 — Conjecture (statement only).**

Suppose `A ⊂ ℕ` is a minimal basis with positive density.
Is it true that, for any `n ∈ A`, the set of integers which cannot be represented
without using `n` has positive density?
-/
@[category research open, AMS 5]
theorem erdos_330 :
    ∀ (h : ℕ) (A : Set ℕ),
      2 ≤ h →
      Basis A h →
      A.HasPosDensity →
      (∀ n ∈ A, (UnrepWithout A h n).HasPosDensity) := by
  sorry

end Erdos330
