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
# Toronto spaces

A *Toronto space* is a topological space
which is homeomorphic to all of its subspaces of same cardinality.

It is conjectured that every T2, Toronto space is discrete.
W.R. Brian proved that this holds under GCH.

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Toronto_space)
 - [The Toronto problem](https://wrbrian.wordpress.com/wp-content/uploads/2012/01/thetorontoproblem.pdf) by *W.R. Brian*
-/

namespace Toronto

open Cardinal

variable (X : Type*) [TopologicalSpace X]

/-- A *Toronto space* is a topological space
which is homeomorphic to all of its subspaces of same cardinality.
-/
class TorontoSpace where
  toronto : ∀ ⦃Y : Set X⦄, #Y = #X → Y ≃ₜ X

/-- Every finite space is Toronto, since
the only subspace with same cardinality is the space itself.
-/
@[category test, AMS 54]
instance Finite.torontoSpace [Finite X] : TorontoSpace X where
  toronto := by
    intro Y hY
    have eq : Y = Set.univ := by
      refine (Set.eq_univ_iff_ncard Y).mpr ?_
      have : Y.ncard = (#↑Y).toNat := by
        exact rfl
      rw [this, hY]
      exact rfl
    rw [eq]
    exact Homeomorph.Set.univ X

/-- Any T2, Toronto space is discrete. -/
@[category research open, AMS 54]
theorem DiscreteTopology.of_t2_of_torontoSpace [T2Space X] [TorontoSpace X] :
    DiscreteTopology X := by
  sorry

-- TODO: Add implication that this holds under the GCH

end Toronto
