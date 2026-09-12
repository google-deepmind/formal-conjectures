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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.RationalCohomologyZero

/-!
# Derived supported sections and rational support hypercohomology

The comparison below starts from the right-derived supported-sections functor on `D⁺` and
passes through the standard rational injective resolution, via its augmentation
quasi-isomorphism, the derived unit, and the normalized cone comparison. The underlying
cone comparisons preserve the connecting morphisms, with the standard cone triangle's
negative projection corrected explicitly. The support-forgetting square, with its
derived-unit and ordinary rational-cohomology comparison, is in
`DerivedSupportRationalForget`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance derivedRationalComparisonSheafCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance derivedRationalComparisonGroupCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- The ambient resolution as a bounded-below complex of genuinely injective
objects. Its boundedness is inherited from extension of a nonnegative
resolution, rather than supplied as a new assumption. -/
def ambientRationalInjectivePlus :
    CochainComplex.Plus (InjectiveObject (AnalyticAdditiveSheaf X)) := by
  let I := HomologicalComplex.liftObjectProperty
    (Injective : AnalyticAdditiveSheaf X → Prop)
    (ambientRationalInjectiveComplex X) (fun _ => inferInstance)
  have hI : CochainComplex.IsStrictlyGE I 0 := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      I (InjectiveObject.ι (AnalyticAdditiveSheaf X))]
    exact ambientRationalInjectiveComplex_isStrictlyGE X
  exact ⟨I, 0, hI⟩

/-- The actual `D⁺` object of the standard ambient injective resolution. -/
def ambientRationalInjectiveDerivedPlus :
    DerivedCategory.Plus (AnalyticAdditiveSheaf X) :=
  DerivedCategory.Plus.Qh.obj
    ((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomotopyCategoryPlus.obj
      ((HomotopyCategory.Plus.quotient _).obj (ambientRationalInjectivePlus X)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The augmentation provides the canonical isomorphism from actual constant
rationals in `D⁺` to their standard injective model. -/
def constantRationalToInjectiveDerivedPlusIso :
    (DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
      (constantFieldSheaf ℚ X) ≅
        ambientRationalInjectiveDerivedPlus X :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ (AnalyticAdditiveSheaf X) 0).app _ ≪≫
      DerivedCategory.Q.mapIso (constantRationalSheafComplexIntIsoSingleZero X).symm ≪≫
      asIso (DerivedCategory.Q.map (ambientRationalInjectiveAugmentation X)) ≪≫
      (DerivedCategory.quotientCompQhIso (AnalyticAdditiveSheaf X)).symm.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual derived unit computes supported sections of rational constants
by the termwise kernel of restriction on the ambient injective resolution. -/
def derivedRationalSupportInjectiveModelIso
    (Z : Closeds (TopCat.of (ComplexPoint X))) :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X))) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) Z.compl ⊤
        (ambientRationalInjectiveComplex X)).X₁ :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedClosedSupportSections
      (TopCat.of (ComplexPoint X)) Z).mapIso
      (constantRationalToInjectiveDerivedPlusIso X)) ≪≫
    TopCat.Sheaf.derivedClosedSupportInjectiveModelIso
      (TopCat.of (ComplexPoint X)) Z (ambientRationalInjectivePlus X)

/-- The actual `D⁺` derived-support group agrees with the repository's rational
support hypercohomology. This is constructed from the constant augmentation,
derived unit, and normalized restriction-cone maps. -/
def derivedRationalSupportAddEquiv
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)))) ≃+
      RationalCohomologyWithSupport X Z n :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
    (derivedRationalSupportInjectiveModelIso X Z) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _).addCommGroupIsoToAddEquiv).trans
    (rationalSupportAddEquivSupportedInjectiveHomology X Z Z.isClosed n).symm

end AlgebraicGeometry.ComplexPoint
