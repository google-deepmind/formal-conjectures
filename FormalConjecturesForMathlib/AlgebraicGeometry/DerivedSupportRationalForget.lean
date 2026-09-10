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

public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusInjectiveModel
public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupportForget
public import FormalConjecturesForMathlib.AlgebraicGeometry.DerivedSupportRationalComparison
public import FormalConjecturesForMathlib.AlgebraicGeometry.DerivedSupportRationalConeForget

/-! # The actual derived support-forgetting square for rational coefficients -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance derivedRationalForgetSheafCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance derivedRationalForgetGroupCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual derived global sections of rational constants, computed using
the standard ambient rational resolution and the actual derived unit. -/
def derivedRationalGlobalInjectiveModelIso :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X))).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X))) ≅
    DerivedCategory.Q.obj
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)) :=
  DerivedCategory.Plus.ι.mapIso
    ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X))).mapIso
      (constantRationalToInjectiveDerivedPlusIso X)) ≪≫
    Functor.rightDerivedFunctorPlusInjectiveModelIso
      (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤)
      (ambientRationalInjectivePlus X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical ordinary-cohomology counterpart of the supported
comparison, with the actual rational augmentation normalization. -/
def derivedRationalCohomologyAddEquiv (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedGlobalSections (TopCat.of (ComplexPoint X))).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)))) ≃+
      FieldCohomology ℚ X n :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
    (derivedRationalGlobalInjectiveModelIso X) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app _).addCommGroupIsoToAddEquiv).trans
    (rationalCohomologyAddEquivAmbientInjectiveHomology X n).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma derivedRationalSupportInjectiveModelIso_forget
    (Z : Closeds (TopCat.of (ComplexPoint X))) :
    DerivedCategory.Plus.ι.map
      ((TopCat.Sheaf.derivedForgetClosedSupport (TopCat.of (ComplexPoint X)) Z).app
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X))) ≫
      (derivedRationalGlobalInjectiveModelIso X).hom =
    (derivedRationalSupportInjectiveModelIso X Z).hom ≫
      DerivedCategory.Q.map
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) Z.compl ⊤
          (ambientRationalInjectiveComplex X)).f := by
  let Y := TopCat.of (ComplexPoint X)
  let I := ambientRationalInjectivePlus X
  have hi := NatTrans.rightDerivedFunctorPlusInjectiveModel_naturality
    (TopCat.Sheaf.closedSupportSectionsInclusion Y Z) I
  have hm : ((TopCat.Sheaf.closedSupportSectionsInclusion Y Z).mapHomologicalComplex
      (.up ℤ)).app
        (((InjectiveObject.ι (AnalyticAdditiveSheaf X)).mapHomologicalComplex
          (.up ℤ)).obj I.obj) =
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
        (ambientRationalInjectiveComplex X)).f := by
    ext n
    simp [TopCat.Sheaf.closedSupportSectionsInclusion,
      TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex,
      TopCat.Sheaf.supportRestrictionComplexShortComplex]
    rfl
  rw [hm] at hi
  have hn := (TopCat.Sheaf.derivedForgetClosedSupport Y Z).naturality
    (constantRationalToInjectiveDerivedPlusIso X).hom
  dsimp only [derivedRationalGlobalInjectiveModelIso,
    derivedRationalSupportInjectiveModelIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]
  exact congrArg (fun f => DerivedCategory.Plus.ι.map
    ((TopCat.Sheaf.derivedClosedSupportSections Y Z).map
      (constantRationalToInjectiveDerivedPlusIso X).hom) ≫ f) hi

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
set_option maxRecDepth 4000 in
/-- The actual `D⁺` support-forgetting inclusion agrees with the repository's
existing `forgetSupport`, under the constructed supported and ordinary
rational comparisons. Both the derived-unit square and the cone signs are
proved, with no supplied compatibility input. -/
lemma derivedRationalSupportAddEquiv_forgetSupport
    (Z : Closeds (TopCat.of (ComplexPoint X))) (n : ℤ)
    (x : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).obj
      ((TopCat.Sheaf.derivedClosedSupportSections
        (TopCat.of (ComplexPoint X)) Z).obj
        ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
          (constantFieldSheaf ℚ X)))) :
    derivedRationalCohomologyAddEquiv X n
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedForgetClosedSupport (TopCat.of (ComplexPoint X)) Z).app
          ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
            (constantFieldSheaf ℚ X))) x) =
    forgetSupport X Z n (derivedRationalSupportAddEquiv X Z n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
    (ambientRationalInjectiveComplex X)
  let H := DerivedCategory.homologyFunctor AddCommGrpCat n
  have hm := congrArg (fun f => H.map f ≫
      ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₂).hom)
    (derivedRationalSupportInjectiveModelIso_forget X Z)
  simp only [Functor.map_comp, Category.assoc] at hm
  have hf := (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).hom.naturality S.f
  have hm' := hm.trans (congrArg
    (fun f => H.map (derivedRationalSupportInjectiveModelIso X Z).hom ≫ f) hf)
  let eS := (H.mapIso (derivedRationalSupportInjectiveModelIso X Z) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₁).addCommGroupIsoToAddEquiv
  let eG := (H.mapIso (derivedRationalGlobalInjectiveModelIso X) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app S.X₂).addCommGroupIsoToAddEquiv
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X n).injective
  calc
    _ = eG ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat n).map
        ((TopCat.Sheaf.derivedForgetClosedSupport Y Z).app
          ((DerivedCategory.Plus.singleFunctor (AnalyticAdditiveSheaf X) 0).obj
            (constantFieldSheaf ℚ X))) x) :=
      (rationalCohomologyAddEquivAmbientInjectiveHomology X n).apply_symm_apply _
    _ = HomologicalComplex.homologyMap S.f n (eS x) :=
      ConcreteCategory.congr_hom hm' x
    _ = _ := by
      rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
        X Z Z.isClosed n]
      exact congrArg (fun y => HomologicalComplex.homologyMap S.f n y)
        (AddEquiv.apply_symm_apply
          (rationalSupportAddEquivSupportedInjectiveHomology X Z Z.isClosed n)
          (eS x)).symm

end AlgebraicGeometry.ComplexPoint
