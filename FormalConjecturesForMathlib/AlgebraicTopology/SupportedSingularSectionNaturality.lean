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

public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSectionRestrictionConeNaturality
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSingularSectionCohomology
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainOpenConeNaturality
public import FormalConjecturesForMathlib.AlgebraicTopology.SupportRelativeCohomologySheaf

/-! # Naturality of actual supported singular-section relative cohomology -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

open TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (U : Opens X) {V W : Opens X} (a : W ⟶ V)

/-- The actual two-step supported kernel and grading comparison, before the relative calculation. -/
def supportedSingularSectionConeHomologyIso (V : Opens X) (n : ℤ) :
    ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X U))).homology n ≅
        (openSingularSheafRestrictionCone ℚ X (Opens.infLELeft V U)).homology (n - 1) :=
  supportedSectionHomologyIsoRestrictionCone X U V (rationalSingularCochainComplex X)
    (fun _ => inferInstance) n ≪≫
  HomologicalComplex.homologyMapIso (sectionComplexRestrictionExtendConeIso X
    (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U)) (n - 1)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual supported kernel-to-singular-cone comparison respects open restriction. -/
@[reassoc]
lemma supportedSingularSectionConeHomologyIso_naturality (n : ℤ) :
    HomologicalComplex.homologyMap
      (sectionComplexRestriction X (.up ℤ) (supportedRationalSingularCochainComplex X U) a) n ≫
      (supportedSingularSectionConeHomologyIso X U W n).hom =
    (supportedSingularSectionConeHomologyIso X U V n).hom ≫
      HomologicalComplex.homologyMap
        (openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
          a (homOfLE (inf_le_inf_right U (leOfHom a)))) (n - 1) := by
  dsimp only [supportedSingularSectionConeHomologyIso, Iso.trans_hom]
  change HomologicalComplex.homologyMap
      (supportRestrictionSectionsComplexMap X U (rationalSingularCochainComplex X) a).τ₁ n ≫
      ((supportedSectionHomologyIsoRestrictionCone X U W (rationalSingularCochainComplex X)
        (fun _ => inferInstance) n).hom ≫ _) = _
  rw [supportedSectionHomologyIsoRestrictionCone_naturality_assoc X U
    (rationalSingularCochainComplex X) a]
  simp only [Category.assoc]
  congr 1
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (n - 1)
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp]
  exact congrArg H.map (sectionComplexRestrictionExtendConeIso_naturality X
    (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U) (Opens.infLELeft W U)
    a (homOfLE (inf_le_inf_right U (leOfHom a))))

/-- Restriction naturality of the entire existing supported-section-to-relative equivalence. -/
lemma supportedRationalSingularSectionCohomologyEquivRelative_naturality
    (n : ℕ)
    (z : ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X U))).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivRelative X U W n
      (HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ) (supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    relativeCohomologyMap ℚ n
      (openInclusionPairMap X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a))))
      (supportedRationalSingularSectionCohomologyEquivRelative X U V n z) := by
  change openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft W U) n
      ((supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
        (HomologicalComplex.homologyMap
          (sectionComplexRestriction X (.up ℤ) (supportedRationalSingularCochainComplex X U) a)
            (n : ℤ) z)) = _
  have h := congrArg (fun f => f z)
    (supportedSingularSectionConeHomologyIso_naturality X U a (n : ℤ))
  change (supportedSingularSectionConeHomologyIso X U W (n : ℤ)).hom
      (HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ) (supportedRationalSingularCochainComplex X U) a)
          (n : ℤ) z) =
    HomologicalComplex.homologyMap
      (openSingularSheafRestrictionConeMap ℚ X (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a)))) ((n : ℤ) - 1)
      ((supportedSingularSectionConeHomologyIso X U V (n : ℤ)).hom z) at h
  rw [h]
  exact openSingularSheafRestrictionConeCohomologyEquivRelative_naturality X
    (Opens.infLELeft V U) (Opens.infLELeft W U) a
    (homOfLE (inf_le_inf_right U (leOfHom a))) n _

omit [T2Space X] [∀ V : Opens X, ParacompactSpace V] in
/-- Regrouping the intersection witnesses commutes with the actual pair inclusions. -/
lemma openIntersectionPairIsoSupportComplement_naturality
    (S : Set X) (hS : IsClosed S) {V W : Opens X} (a : W ⟶ V) :
    openInclusionPairMap X
      (Opens.infLELeft V (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X))
      (Opens.infLELeft W (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X))
      a (homOfLE (inf_le_inf_right _ (leOfHom a))) ≫
        (openIntersectionPairIsoSupportComplement X S hS V).hom =
    (openIntersectionPairIsoSupportComplement X S hS W).hom ≫
      neighborhoodSupportInclusionPairMap
        (W := (W : Set X)) (V := (V : Set X)) (leOfHom a) S := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- The final support-complement comparison preserves literal ambient-open restrictions. -/
lemma supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
    (S : Set X) (hS : IsClosed S) {V W : Opens X} (a : W ⟶ V) (n : ℕ)
    (z : ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS W n
      (HomologicalComplex.homologyMap
        (sectionComplexRestriction X (.up ℤ)
          (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) a) (n : ℤ) z) =
    relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap
        (W := (W : Set X)) (V := (V : Set X)) (leOfHom a) S)
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z) := by
  change relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X S hS W).inv
      (supportedRationalSingularSectionCohomologyEquivRelative X _ W n _) =
    relativeCohomologyMap ℚ n _
      (relativeCohomologyMap ℚ n (openIntersectionPairIsoSupportComplement X S hS V).inv
        (supportedRationalSingularSectionCohomologyEquivRelative X _ V n z))
  rw [supportedRationalSingularSectionCohomologyEquivRelative_naturality,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← relativeCohomologyMap_comp]
  congr 2

end AlgebraicTopology.Singular
