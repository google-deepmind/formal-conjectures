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
# Erdős Problem 741

*References:*
 - [erdosproblems.com/741](https://www.erdosproblems.com/741)
 - [Er94b] Erdős, Paul, Some problems in number theory, combinatorics and combinatorial geometry.
    Math. Pannon. (1994), 261-269.
-/

open scoped Pointwise
open Set

namespace Erdos741

/-- Let `A ⊆ ℕ` be a set such that `A + A` has positive density. Can one always decompose
`A` as a disjoint union of two subsets `A₁` and `A₂` such that both `A₁ + A₁` and `A₂ + A₂` have
positive density? -/
@[category research open, AMS 5]
theorem erdos_741.density : answer(sorry) ↔ ∀ A : Set ℕ, HasPosDensity (A + A) → ∃ A₁ A₂,
    A₁ ⊆ A ∧ A₂ ⊆ A ∧ A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ HasPosDensity (A₁ + A₁)
    ∧ HasPosDensity (A₂ + A₂):= by
  sorry

/-- Let `A ⊆ ℕ` be a basis of order 2. Can one always decompose `A` as a disjoint union of two
subsets `A₁` and `A₂` such that `A₁ + A₁` and `A₂ + A₂` cannot both have bounded gaps? -/
@[category research open, AMS 5]
theorem erdos_741.basis : answer(sorry) ↔ ∀ A : Set ℕ, IsAddBasisOfOrder (A ∪ {0}) 2 → ∃ A₁ A₂,
    A₁ ⊆ A ∧ A₂ ⊆ A ∧ A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧ ¬ (IsSyndetic A₁ ∧ IsSyndetic A₂):= by
  sorry

end Erdos741
