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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.DerivedSupportRationalConeComparison

/-!
# Normalized injective models for the rational support cone

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.DerivedSupportRationalConeComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The old-cone comparison preserves the actual connecting morphism used to
forget support, with the ambient augmentation on its target. -/
@[reassoc]
lemma rationalSupportConeToAmbientInjectiveCone_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalSupportConeToAmbientInjectiveCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle
        (ambientRationalInjectiveRestriction X Z hZ)).mor₃ =
    (CochainComplex.mappingCone.triangle (rationalRestrictionComplexInt X Z)).mor₃ ≫
      (ambientRationalInjectiveAugmentation X)⟦(1 : ℤ)⟧' :=
  (CochainComplex.mappingCone.triangleMap _ _
    (ambientRationalInjectiveAugmentation X) (𝟙 _)
    (by simpa using (ambientRationalAugmentation_comp_restriction X Z hZ).symm)).comm₃.symm

/-- Both resolutions, and hence their cone, are termwise flasque. -/
lemma ambientRationalInjectiveCone_isFlasque
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (q : ℤ) :
    ((CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z hZ)).X q).IsFlasque := by
  apply TopCat.Sheaf.IsFlasque.BoundedBelowComplex.mappingCone_term_isFlasque
    (ambientRationalInjectiveRestriction X Z hZ)
  · exact fun _ ↦ TopCat.Sheaf.injective_isFlasque _ _
  · exact derivedPushforwardComplementConstantRationalComplexInt_term_isFlasque X Z

set_option backward.isDefEq.respectTransparency false in
/-- The group-cone comparison preserves its connecting morphism with the
identity on the ambient global sections. -/
@[reassoc]
lemma actualSupportConeToAmbientInjectiveGlobalCone_connecting
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    actualSupportConeToAmbientInjectiveGlobalCone X Z hZ ≫
      (CochainComplex.mappingCone.triangle
        (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
            (ambientRationalInjectiveRestriction X Z hZ))).mor₃ =
    (CochainComplex.mappingCone.triangle
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g).mor₃ := by
  have h := (CochainComplex.mappingCone.triangleMap
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
      (ambientRationalInjectiveComplex X)).g
    (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map
        (ambientRationalInjectiveRestriction X Z hZ)) (𝟙 _)
    (globalAmbientRationalOpenResolutionComparison X Z hZ)
    (show _ = _ from by
      let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)
      change Γ.map _ ≫ Γ.map _ = 𝟙 _ ≫ Γ.map _
      rw [Category.id_comp, ← Functor.map_comp,
        actualRestriction_comp_openResolutionComparison])).comm₃
  exact h.symm.trans ((congrArg (fun f =>
    (CochainComplex.mappingCone.triangle
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).g).mor₃ ≫ f)
    ((shiftFunctor (CochainComplex AddCommGrpCat ℤ) (1 : ℤ)).map_id _)).trans
      (Category.comp_id _))

end AlgebraicGeometry.ComplexPoint
