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

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The canonical homotopy fiber comparison for a short exact sequence

For `0 → A → B → C → 0` this file constructs the canonical quasi-isomorphism
`A → mappingCocone (B → C)`. Its normalization is the actual inclusion `A → B`.
The proof uses the explicit mapping-cone rotation homotopy equivalence and the
canonical quasi-isomorphism from the cone of `A → B` to `C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace mappingCone

end mappingCone

namespace mappingCocone

variable (S : ShortComplex (CochainComplex C ℤ))

/-- The explicit rotated-cone comparison, before shifting back to the homotopy
fiber. It is built from canonical chain maps, not from a choice of a completion
of a morphism of distinguished triangles. -/
def shiftedLiftShortComplex : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

/-- Canonical comparison from the first term of a short complex to the homotopy
fiber of its second map. -/
def liftShortComplex : S.X₁ ⟶ mappingCocone S.g :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).inv.app S.X₁ ≫
    (shiftedLiftShortComplex S)⟦(-1 : ℤ)⟧'

end mappingCocone

end CochainComplex
