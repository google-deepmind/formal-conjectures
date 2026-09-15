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
module

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CohomologyWithSupport

/-!
# Rational cohomology with support

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CohomologyWithSupport`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticSupportHasDerivedCategory

section

end

@[simp] lemma forgetSupportEquivUniv_apply (n : ℤ)
    (α : RationalCohomologyWithSupport X
      (Set.univ : Set (ComplexPoint X)) n) :
    forgetSupportEquivUniv X n α =
      forgetSupport X Set.univ n α := rfl

/-- Forgetting whole-space support is surjective. -/
lemma forgetSupport_surjective_univ (n : ℤ) :
    Function.Surjective
      (forgetSupport X (Set.univ : Set (ComplexPoint X)) n) := by
  intro α
  obtain ⟨β, hβ⟩ := (forgetSupportEquivUniv X n).surjective α
  exact ⟨β, (forgetSupportEquivUniv_apply X n β).symm.trans hβ⟩

end AlgebraicGeometry.ComplexPoint
