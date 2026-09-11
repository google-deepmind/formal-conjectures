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

public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNaturality
public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShift

/-!
# Shift compatibility of derived natural transformations

The transformations induced by coefficient maps commute with the actual coherent
shifts. This is needed to compare support enlargement before and after orientation
duality. The compatibility is proved on complexes and descended through the actual
injective-resolution comparison, not supplied as data.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.NatTrans

section Detect

variable {B C D : Type*} [Category* B] [Category* C] [Category* D]
  (A : Type*) [AddMonoid A] [HasShift B A] [HasShift C A] [HasShift D A]

/-- Shift compatibility can be checked after essentially surjective precomposition. -/
lemma commShift_of_whiskerLeft (L : B ⥤ C) [L.EssSurj] [L.CommShift A]
    {F G : C ⥤ D} [F.CommShift A] [G.CommShift A] (α : F ⟶ G)
    [CommShift (Functor.whiskerLeft L α) A] : CommShift α A where
  shift_comm a := by
    let τ := (F.commShiftIso a).hom ≫ Functor.whiskerRight α _
    let τ' := Functor.whiskerLeft _ α ≫ (G.commShiftIso a).hom
    have h (X : B) : τ.app (L.obj X) = τ'.app (L.obj X) := by
      have h := shift_app_comm (Functor.whiskerLeft L α) a X
      simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app,
        Category.assoc] at h
      rw [← α.naturality_assoc] at h
      exact (cancel_epi (F.map ((L.commShiftIso a).hom.app X))).1 h
    change τ = τ'
    ext Y : 2
    rw [← cancel_epi ((shiftFunctor C a ⋙ F).map (L.objObjPreimageIso Y).hom),
      τ.naturality, τ'.naturality, h]

/-- Shift compatibility can be checked after faithful postcomposition. -/
lemma commShift_of_whiskerRight (L : C ⥤ D) [L.Faithful] [L.CommShift A]
    {F G : B ⥤ C} [F.CommShift A] [G.CommShift A] (α : F ⟶ G)
    [CommShift (Functor.whiskerRight α L) A] : CommShift α A where
  shift_comm a := by
    ext X : 2
    apply L.map_injective
    apply (cancel_mono ((L.commShiftIso a).hom.app (G.obj X))).1
    have h := shift_app_comm (Functor.whiskerRight α L) a X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app,
      Category.assoc] at h
    rw [← L.commShiftIso_hom_naturality] at h
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, L.map_comp, Category.assoc] using h

end Detect

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Termwise coefficient transformations commute with cohomological shifts. -/
instance mapCochainComplexCommShift : CommShift (α.mapHomologicalComplex (.up ℤ)) ℤ where
  shift_comm a := by
    ext K i
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The induced transformation on homotopy categories retains the actual shifts. -/
instance mapHomotopyCategoryCommShift : CommShift (α.mapHomotopyCategory (.up ℤ)) ℤ := by
  have h : Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (α.mapHomotopyCategory (.up ℤ)) =
      (F.mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        Functor.whiskerRight (α.mapHomologicalComplex (.up ℤ))
          (HomotopyCategory.quotient D (.up ℤ)) ≫
        (G.mapHomotopyCategoryFactors (.up ℤ)).inv := by
    ext K
    simp [Functor.mapHomotopyCategoryFactors, mapHomotopyCategory]
    exact (Category.id_comp _).symm
  have : CommShift (Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (α.mapHomotopyCategory (.up ℤ))) ℤ := by
    rw [h]
    infer_instance
  exact commShift_of_whiskerLeft ℤ (HomotopyCategory.quotient C (.up ℤ)) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting to bounded-below homotopy complexes preserves shift compatibility. -/
instance mapHomotopyCategoryPlusCommShift : CommShift α.mapHomotopyCategoryPlus ℤ := by
  let eF : F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ≅
      HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (.up ℤ) :=
    (HomotopyCategory.plus D).liftCompιIso _ _
  let eG : G.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ≅
      HomotopyCategory.Plus.ι C ⋙ G.mapHomotopyCategory (.up ℤ) :=
    (HomotopyCategory.plus D).liftCompιIso _ _
  have : CommShift eF.hom ℤ := by dsimp [eF]; infer_instance
  have : CommShift eG.hom ℤ := by dsimp [eG]; infer_instance
  have h : Functor.whiskerRight α.mapHomotopyCategoryPlus (HomotopyCategory.Plus.ι D) =
      eF.hom ≫ Functor.whiskerLeft (HomotopyCategory.Plus.ι C)
        (α.mapHomotopyCategory (.up ℤ)) ≫ eG.inv := by
    ext K
    simp [eF, eG, mapHomotopyCategoryPlus, ObjectProperty.liftCompιIso]
    exact (Category.id_comp _).symm
  have : CommShift (Functor.whiskerRight α.mapHomotopyCategoryPlus
      (HomotopyCategory.Plus.ι D)) ℤ := by
    rw [h]
    infer_instance
  exact commShift_of_whiskerRight ℤ (HomotopyCategory.Plus.ι D) _

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On injective complexes the derived transformation is the actual termwise map,
conjugated by the canonical derived-unit isomorphisms. -/
theorem rightDerivedFunctorPlus_onInjectives :
    Functor.whiskerLeft (HomotopyCategory.Plus.injectiveToDerived C)
        α.rightDerivedFunctorPlus =
      F.rightDerivedFunctorPlusOnInjectivesIso.hom ≫
        Functor.whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
          (Functor.whiskerRight α.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh) ≫
        G.rightDerivedFunctorPlusOnInjectivesIso.inv := by
  ext K : 2
  apply (cancel_epi ((asIso F.rightDerivedFunctorPlusOnInjectivesUnit).app K).hom).1
  simp [Functor.rightDerivedFunctorPlusOnInjectivesIso,
    Functor.rightDerivedFunctorPlusOnInjectivesUnit,
    HomotopyCategory.Plus.injectiveToDerived]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Coherent shift compatibility of the actual derived transformation. No shift
compatibility of the coefficient map is supplied: it was proved termwise above. -/
instance rightDerivedFunctorPlusCommShift : CommShift α.rightDerivedFunctorPlus ℤ := by
  have : CommShift (Functor.whiskerLeft (HomotopyCategory.Plus.injectiveToDerived C)
      α.rightDerivedFunctorPlus) ℤ := by
    rw [rightDerivedFunctorPlus_onInjectives]
    infer_instance
  exact commShift_of_whiskerLeft ℤ (HomotopyCategory.Plus.injectiveToDerived C) _

end CategoryTheory.NatTrans
