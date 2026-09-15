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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LowestFlasqueCohomology

/-!
# The actual lowest-degree cohomology comparison for flasque complexes

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.LowestFlasqueCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

@[simp] theorem lowestSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque)
    (U : Opens X) :
    (lowestSectionCohomologyIso X K N n hK hflasque U).hom =
      sectionCohomologyToSheafSection X K n U := rfl

@[simp] theorem lowestGlobalSectionCohomologyIso_hom (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j)) (hflasque : ∀ j, (K.X j).IsFlasque) :
    (lowestGlobalSectionCohomologyIso X K N n hK hflasque).hom =
      sectionCohomologyToSheafSection X K n ⊤ := rfl

end TopCat.Sheaf
