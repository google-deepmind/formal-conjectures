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
# Finiteness of finitely presented periodic groups

A *periodic group* is a group in which every element has finite order.
The conjecture asks whether every finitely presented periodic group is finite.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Periodic_group)
-/

namespace FinitenessPeriodicGroups

/-- A group is *periodic* if every element has finite order. -/
def IsPeriodic (G : Type*) [Group G] : Prop :=
  ∀ g : G, IsOfFinOrder g

/-- If $G$ is a finitely generated periodic group, must $G$ be finite?

Note: The full conjecture asks about finitely *presented* groups. Since Mathlib does not
yet have a standard definition of "finitely presented group", we state this with the
weaker condition of finitely generated (`Group.FG`). The original conjecture with
"finitely presented" is strictly stronger.
-/
@[category research open, AMS 20]
theorem finiteness_periodic_groups :
    answer(sorry) ↔ ∀ (G : Type) [Group G] (_ : Group.FG G)
      (_ : IsPeriodic G), Finite G := by
  sorry

end FinitenessPeriodicGroups
