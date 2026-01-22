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
# Conjecture about cardinality of Lindelöf spaces

The conjecture asks for a Lindelöf space where all singletons are G_δ sets
and which has cardinality > 𝔠.

This is Problem 1 in https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf

*Reference:*
* [Selected Old Open Problems in General Topology](https://www.math.md/files/basm/y2013-n2-3/y2013-n2-3-(pp37-46).pdf.pdf)
  by A. V. Arhangel’skii

-/

open Cardinal

namespace CardinalityLindelof

/--
A space where all singletons are Gδ points.
-/
class HasSingletonsGδ (X : Type*) [TopologicalSpace X] : Prop where
  gδPoints : ∀ ⦃x : X⦄, IsGδ {x}

/-- Singletons are Gδ in First-Countable T₁ Spaces -/
@[category test, AMS 54]
instance HasPointsGδ.ofT1SpaceFirstCountable (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] [T1Space X] : HasSingletonsGδ X where
  gδPoints := IsGδ.singleton

/--
Does every Lindelöf space with Gδ points have cardinality less or equal to the continuum?
-/
@[category research open, AMS 54]
theorem HasPointsGδ.lindelof_card :
    ∃ (X : Type*) (_ : TopologicalSpace X), HasSingletonsGδ X ∧ LindelofSpace X ∧ 𝔠 < #X := by
  sorry

--TODO under additional set theory axioms, there exists such a space with 𝔠 < #X.

end CardinalityLindelof
