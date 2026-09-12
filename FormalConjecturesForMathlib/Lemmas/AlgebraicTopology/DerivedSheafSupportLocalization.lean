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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.DerivedSheafSupportLocalization

/-!
# The actual localization sequence on injective coefficient complexes

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.DerivedSheafSupportLocalization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- The localization comparison preserves the actual support-forgetting map,
including its sign. -/
@[reassoc (attr := simp)]
lemma supportRestrictionToFiber_fst (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    supportRestrictionToFiber X U V K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionSectionsComplexShortComplex X U V K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

@[reassoc (attr := simp)]
lemma sheafSupportRestrictionToFiber_fst
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    sheafSupportRestrictionToFiber X U K ≫ CochainComplex.mappingCocone.fst _ =
      (supportRestrictionComplexShortComplex X U K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

attribute [local instance] derivedSupportLocalizationSheafDerivedCategory

attribute [local instance] derivedSupportLocalizationGroupDerivedCategory

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedClosedSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedClosedSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedClosedSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionSectionsComplexShortComplex X Z.compl ⊤
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedClosedSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma derivedSheafSupportInjectiveFiberIso_hom_fst (Z : Closeds X)
    (I : CochainComplex.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    (derivedSheafSupportInjectiveFiberIso X Z I).hom ≫
      DerivedCategory.Q.map (CochainComplex.mappingCocone.fst _) =
    (derivedSheafSupportInjectiveModelIso X Z I).hom ≫
      DerivedCategory.Q.map
        (supportRestrictionComplexShortComplex X Z.compl
          (((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex
            (.up ℤ)).obj I.obj)).f := by
  simp [derivedSheafSupportInjectiveFiberIso, ← DerivedCategory.Q.map_comp]

end TopCat.Sheaf
