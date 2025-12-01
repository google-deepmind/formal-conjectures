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
# Chvátal's Conjecture

*References:*

* [A Conjecture in Extremal Combinatorics](https://users.encs.concordia.ca/~chvatal/conjecture.html)
* [Chvátal's Conjecture and Correlation Inequalities](https://arxiv.org/abs/1608.08954)
-/

namespace Chvatal

variable {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]

/-- A family F of sets is Decreasing if it is closed under taking subsets. -/
def Decreasing (F : Finset (Finset α)) : Prop :=
    ∀ A B : Finset α, B ⊆ A → A ∈ F → B ∈ F

/-- A family F of sets is Intersecting if each pair of members has nonempty intersection. -/
def Intersecting (F : Finset (Finset α)) : Prop :=
    ∀ A ∈ F, ∀ B ∈ F, A ∩ B ≠ ∅

/--
If F is a decreasing family of sets of some finite type α, then there is some element
x of α such that the family consisting of all members of F containing x is an intersecting
subfamily of F with maximal cardinality.
-/
@[category research open, AMS 5]
theorem exists_maximal_star
    : ∀ F : Finset (Finset α), Decreasing F →
        ∃ x : α, ∀ G, G ⊆ F → Intersecting G → G.card ≤ { A ∈ F | x ∈ A }.card := by
  sorry
