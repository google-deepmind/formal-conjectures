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
# Leinster groups

A *Leinster group* is a finite group whose sum of orders of all subgroups
equals the square of the order of the group.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Leinster_group)
-/

namespace LeinsterGroup

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

/-- A finite group `G` is a *Leinster group* if the sum of the orders of all its
subgroups equals the square of the order of the group:
$$\sum_{H \leq G} |H| = |G|^2$$
-/
def IsLeinsterGroup : Prop :=
  ∑ H : Subgroup G, Nat.card H = (Fintype.card G) ^ 2

/-- A Leinster group of a given order exists. -/
def ExistsLeinsterGroupOfOrder (n : ℕ) : Prop :=
  ∃ (G : Type) (hG : Group G) (hF : Fintype G) (hD : DecidableEq G),
    @Fintype.card G hF = n ∧ @IsLeinsterGroup G hG hF hD

/-- Are there infinitely many Leinster groups?

We formulate this as: the set of natural numbers that are orders of Leinster groups
is infinite. -/
@[category research open, AMS 20]
theorem leinster_group_conjecture :
    answer(sorry) ↔ Set.Infinite {n : ℕ | ExistsLeinsterGroupOfOrder n} := by
  sorry

end LeinsterGroup
