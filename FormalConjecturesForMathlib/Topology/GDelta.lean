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
