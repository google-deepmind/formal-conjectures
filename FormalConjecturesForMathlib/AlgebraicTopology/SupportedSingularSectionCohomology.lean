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

public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSectionRestrictionCone
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularFlasqueSupportModel
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainOpenCone
public import FormalConjecturesForMathlib.AlgebraicTopology.FlattenedSupportLocalHomology

/-!
# Actual supported singular-section cohomology on arbitrary opens

The actual kernel of restriction on singular cochain sheaves is compared to the literal
relative singular pair on an arbitrary open neighborhood. The construction composes the
proved flasque kernel/cone comparison, canonical grading comparison, and the actual
sheafification-unit cone comparison. It assumes no local purity or orientation theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

/-- The literal intersection subspace and the complement of a support inside an open
are homeomorphic by regrouping subtype witnesses. -/
def openIntersectionSupportComplementHomeomorph (S : Set X) (hS : IsClosed S) (V : Opens X) :
    ↥(V ⊓ (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≃ₜ {v : V | v.1 ∉ S} where
  toEquiv := (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ V) (· ∉ S)).symm
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The actual open-inclusion pair is the actual support-complement pair, preserving
the ambient open pointwise. -/
def openIntersectionPairIsoSupportComplement (S : Set X) (hS : IsClosed S) (V : Opens X) :
    openInclusionPair X (Opens.infLELeft V (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X)) ≅
      neighborhoodSupportComplementPair (V : Set X) S where
  hom := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨openIntersectionSupportComplementHomeomorph X S hS V,
      (openIntersectionSupportComplementHomeomorph X S hS V).continuous⟩) rfl
  inv := TopPair.ofHom (𝟙 (TopCat.of V))
    (TopCat.ofHom ⟨(openIntersectionSupportComplementHomeomorph X S hS V).symm,
      (openIntersectionSupportComplementHomeomorph X S hS V).symm.continuous⟩) rfl
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V] (U V : Opens X)

/-- Actual local supported singular cohomology computes the literal relative pair
`(V, V ∩ U)`, in supported degree `n`. -/
def supportedRationalSingularSectionCohomologyEquivRelative (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X U))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (openInclusionPair X (Opens.infLELeft V U)) n :=
  (TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone X U V
      (rationalSingularCochainComplex X) (fun _ => inferInstance) (n : ℤ)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (HomologicalComplex.homologyMapIso
    (TopCat.Sheaf.sectionComplexRestrictionExtendConeIso X
      (singularCochainSheafComplex ℚ X) (Opens.infLELeft V U))
        ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans (openSingularSheafRestrictionConeCohomologyEquivRelative X (Opens.infLELeft V U) n)

/-- Actual local supported singular cohomology computes `(V, V \ S)`, with the pair
homeomorphism displayed explicitly rather than silently replacing an inclusion. -/
def supportedRationalSingularSectionCohomologyEquivSupportComplement
    (S : Set X) (hS : IsClosed S) (V : Opens X) (n : ℕ) :
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ) ≃+
        RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n :=
  (supportedRationalSingularSectionCohomologyEquivRelative X ⟨Sᶜ, hS.isOpen_compl⟩ V n).trans
    (((relativeHomologyFunctor ℚ n).mapIso
      (openIntersectionPairIsoSupportComplement X S hS V).symm).toLinearEquiv.dualMap.toAddEquiv)

end AlgebraicTopology.Singular
