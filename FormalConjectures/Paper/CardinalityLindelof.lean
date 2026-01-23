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
class HasGδSingletons (X : Type*) [TopologicalSpace X] : Prop where
  isGδ_singleton : ∀ ⦃x : X⦄, IsGδ {x}

/-- Singletons are Gδ in First-Countable T₁ Spaces -/
@[category test, AMS 54]
instance HasGδSingletons.of_t1Space_firstCountableTopology (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] [T1Space X] : HasGδSingletons X where
  isGδ_singleton := IsGδ.singleton

/--
Is the a Lindelöf space with Gδ points with  cardinality greater than the continuum?
-/
@[category research open, AMS 54]
theorem HasGδSingletons.lindelof_card :
    ∃ (X : Type) (_ : TopologicalSpace X), HasGδSingletons X ∧ LindelofSpace X ∧ 𝔠 < #X := by
  sorry

-- TODO: under additional axioms, there such a space exists. I.e. this is consistent with ZFC

end CardinalityLindelof
