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

public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNaturality

/-! # Naturality of the actual injective-model computation of `D⁺` right derivation -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluate the actual right derived functor on a bounded-below injective
complex, through its actual derived unit and the localization comparison. -/
def rightDerivedFunctorPlusInjectiveModelIso (F : C ⥤ D) [F.Additive]
    (I : CochainComplex.Plus (InjectiveObject C)) :
    DerivedCategory.Plus.ι.obj
      (F.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≅
    DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj
        (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj)) :=
  (DerivedCategory.Plus.ι.mapIso
    (asIso (F.rightDerivedFunctorPlusUnit.app
      ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
        ((HomotopyCategory.Plus.quotient _).obj I))))).symm ≪≫
    (DerivedCategory.quotientCompQhIso D).app _

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma rightDerivedFunctorPlusInjectiveModel_naturality
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    (I : CochainComplex.Plus (InjectiveObject C)) :
    DerivedCategory.Plus.ι.map
      (α.rightDerivedFunctorPlus.app
        (DerivedCategory.Plus.Qh.obj
          ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient _).obj I)))) ≫
      (G.rightDerivedFunctorPlusInjectiveModelIso I).hom =
    (F.rightDerivedFunctorPlusInjectiveModelIso I).hom ≫
      DerivedCategory.Q.map
        ((α.mapHomologicalComplex (.up ℤ)).app
          (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj)) := by
  let K := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
    ((HomotopyCategory.Plus.quotient _).obj I)
  have hu : α.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Qh.obj K) ≫
      inv (G.rightDerivedFunctorPlusUnit.app K) =
      inv (F.rightDerivedFunctorPlusUnit.app K) ≫
        DerivedCategory.Plus.Qh.map (α.mapHomotopyCategoryPlus.app K) := by
    apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).1
    rw [← Category.assoc, rightDerivedFunctorPlus_unit_app,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  dsimp only [Functor.rightDerivedFunctorPlusInjectiveModelIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, asIso_inv,
    Category.assoc]
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc]
  congr 1
  exact (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((α.mapHomologicalComplex (.up ℤ)).app
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj I.obj))

end CategoryTheory.NatTrans
