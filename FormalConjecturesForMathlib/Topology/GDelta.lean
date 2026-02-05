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

import Mathlib.Topology.Separation.GDelta

/--
A space where all singletons are Gδ sets.
-/
class HasGδSingletons (X : Type*) [TopologicalSpace X] : Prop where
  isGδ_singleton : ∀ ⦃x : X⦄, IsGδ {x}

/-- Singletons are Gδ in First-Countable T₁ Spaces- -/
instance HasGδSingletons.of_t1Space_firstCountableTopology (X : Type*) [TopologicalSpace X]
    [FirstCountableTopology X] [T1Space X] : HasGδSingletons X where
  isGδ_singleton := IsGδ.singleton
