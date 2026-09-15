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

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Coherent shifts on bounded-below right derived functors

The bounded-below homotopy category of injective objects is equivalent to the
bounded-below derived category. The right-derived unit becomes an isomorphism
on this category. We therefore descend the existing coherent shifts through
this equivalence, using Mathlib's localization construction.

No shift isomorphism is supplied as mathematical input. Boundedness is explicit
in all source and target categories.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HomotopyCategory.Plus

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The bounded-below homotopy category of injective objects maps to the
bounded-below derived category. -/
def injectiveToDerived :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus C :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

instance : (injectiveToDerived C).CommShift ℤ := by
  dsimp only [injectiveToDerived]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma injectiveToDerived_map_bijective
    (K L : HomotopyCategory.Plus (InjectiveObject C)) :
    Function.Bijective ((injectiveToDerived C).map : (K ⟶ L) → _) := by
  let incl := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  have hL : CochainComplex.IsKInjective (incl.obj L).obj.as := by
    obtain ⟨n, hn⟩ : CochainComplex.plus C (incl.obj L).obj.as := by
      have h := (incl.obj L).property
      rwa [← HomotopyCategory.plus_quotient_obj_iff]
    exact CochainComplex.isKInjective_of_injective _ n
  exact (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    (incl.obj K) (incl.obj L) hL).comp ⟨incl.map_injective, incl.map_surjective⟩

instance : (injectiveToDerived C).Full where
  map_surjective := (injectiveToDerived_map_bijective C _ _).surjective

instance : (injectiveToDerived C).Faithful where
  map_injective {K L} {_f _g} h := (injectiveToDerived_map_bijective C K L).injective h

variable [EnoughInjectives C]

instance : (injectiveToDerived C).EssSurj := by
  dsimp only [injectiveToDerived]
  infer_instance

instance : (injectiveToDerived C).IsEquivalence := { }

instance : (injectiveToDerived C).IsLocalization
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) :=
  Functor.IsLocalization.of_isEquivalence _ _ (by rfl)

omit [HasDerivedCategory C] in
/-- Natural transformations into a functor that inverts quasi-isomorphisms are
determined by their values on bounded-below injective complexes. The proof uses
the existing injective resolutions, not an extra resolution hypothesis. -/
lemma natTrans_ext_on_injectives {H : Type*} [Category* H]
    {F G : HomotopyCategory.Plus C ⥤ H}
    (hG : (HomotopyCategory.Plus.quasiIso C).IsInvertedBy G)
    {α β : F ⟶ G}
    (h : ∀ K : HomotopyCategory.Plus (InjectiveObject C),
      α.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K) =
        β.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K)) : α = β := by
  ext K : 2
  let r := Classical.arbitrary ((HomotopyCategory.Plus.localizerMorphism C).RightResolution K)
  have : IsIso (G.map r.w) := hG r.w r.hw
  rw [← cancel_mono (G.map r.w), ← α.naturality, ← β.naturality, h]

end HomotopyCategory.Plus

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive]

/-- Termwise application of `F` to bounded-below injective complexes, followed
by passage to the derived category. -/
def rightDerivedFunctorPlusOnInjectives :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus D :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

instance : F.rightDerivedFunctorPlusOnInjectives.CommShift ℤ := by
  dsimp only [rightDerivedFunctorPlusOnInjectives]
  infer_instance

/-- The right-derived unit restricted to injective complexes. -/
def rightDerivedFunctorPlusOnInjectivesUnit :
    F.rightDerivedFunctorPlusOnInjectives ⟶
      HomotopyCategory.Plus.injectiveToDerived C ⋙ F.rightDerivedFunctorPlus :=
  whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
      F.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : IsIso F.rightDerivedFunctorPlusOnInjectivesUnit := by
  have h (K : HomotopyCategory.Plus (InjectiveObject C)) :
      IsIso (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
        F.rightDerivedFunctorPlusUnit K
  let _ : ∀ K, IsIso (F.rightDerivedFunctorPlusOnInjectivesUnit.app K) := fun K => by
    simpa only [rightDerivedFunctorPlusOnInjectivesUnit, NatTrans.comp_app,
      whiskerLeft_app, Functor.associator_inv_app, Category.comp_id] using h K
  exact NatIso.isIso_of_isIso_app _

/-- The canonical injective-resolution comparison. -/
def rightDerivedFunctorPlusOnInjectivesIso :
    HomotopyCategory.Plus.injectiveToDerived C ⋙ F.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlusOnInjectives :=
  (asIso F.rightDerivedFunctorPlusOnInjectivesUnit).symm

instance rightDerivedFunctorPlusInjectiveLifting :
    Localization.Lifting (HomotopyCategory.Plus.injectiveToDerived C)
      (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C)))
      F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus :=
  ⟨F.rightDerivedFunctorPlusOnInjectivesIso⟩

/-- Coherent shift compatibility of the actual bounded-below right derived
functor. Its zero and addition coherence laws are inherited by localization
from the termwise complex-level shift compatibility. -/
instance rightDerivedFunctorPlusCommShift : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.commShiftOfLocalization (HomotopyCategory.Plus.injectiveToDerived C)
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) ℤ
    F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus

/-- The injective-resolution comparison is compatible with the constructed
coherent shifts. This pins the comparison to the actual derived unit. -/
instance rightDerivedFunctorPlusOnInjectivesIso_commShift :
    NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesIso.hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (HomotopyCategory.Plus.injectiveToDerived C)
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) ℤ
    F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with the derived unit after restriction to injective complexes. -/
instance rightDerivedFunctorPlusUnit_whiskerLeft_injectives_commShift :
    NatTrans.CommShift (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
      F.rightDerivedFunctorPlusUnit) ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesUnit ℤ :=
    inferInstanceAs (NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesIso.inv ℤ)
  have h : F.rightDerivedFunctorPlusOnInjectivesUnit ≫ (Functor.associator _ _ _).hom =
      whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
        F.rightDerivedFunctorPlusUnit := by
    simp [rightDerivedFunctorPlusOnInjectivesUnit]
  rw [← h]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full right-derived unit commutes with the constructed coherent shifts,
including on complexes which are not termwise injective. -/
instance rightDerivedFunctorPlusUnitCommShift :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ where
  shift_comm a := by
    apply HomotopyCategory.Plus.natTrans_ext_on_injectives C
    · intro K L f hf
      have : IsIso (DerivedCategory.Plus.Qh.map f) :=
        Localization.inverts DerivedCategory.Plus.Qh
          (HomotopyCategory.Plus.quasiIso C) f hf
      change IsIso ((shiftFunctor (DerivedCategory.Plus D) a).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map f)))
      infer_instance
    · intro K
      let incl := (InjectiveObject.ι C).mapHomotopyCategoryPlus
      have h := NatTrans.shift_app_comm
        (whiskerLeft incl F.rightDerivedFunctorPlusUnit) a K
      simp only [Functor.commShiftIso_comp_hom_app, whiskerLeft_app, Category.assoc] at h
      rw [← F.rightDerivedFunctorPlusUnit.naturality_assoc] at h
      apply (cancel_epi ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
        ((incl.commShiftIso a).hom.app K))).1
      simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Category.assoc] using h

end CategoryTheory.Functor
