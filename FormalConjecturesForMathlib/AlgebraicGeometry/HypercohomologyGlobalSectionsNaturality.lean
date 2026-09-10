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

public import FormalConjecturesForMathlib.Algebra.Homology.HomComplexPostcompNaturality
public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison

/-! # Naturality of the hypercohomology/global-sections comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma fromSingleZeroIsoPreadditiveCoyoneda_naturality :
    postcompMap ((CochainComplex.singleFunctor C 0).obj A) f ≫
      (fromSingleZeroIsoPreadditiveCoyoneda A L).hom =
    (fromSingleZeroIsoPreadditiveCoyoneda A K).hom ≫
      ((preadditiveCoyoneda.obj (.op A)).mapHomologicalComplex (.up ℤ)).map f := by
  ext n z
  change Cochain.fromSingleEquiv (zero_add n)
      (z.comp (Cochain.ofHom f) (add_zero n)) =
    Cochain.fromSingleEquiv (zero_add n) z ≫ f.f n
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

end CochainComplex.HomComplex

namespace TopCat.Sheaf

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma homComplexSingleIntegerIsoGlobalSections_naturality
    (Y : TopCat.{0}) {K L : CochainComplex (Sheaf AddCommGrpCat Y) ℤ} (f : K ⟶ L) :
    CochainComplex.HomComplex.postcompMap (integerConstantSingleComplex Y) f ≫
      (homComplexSingleIntegerIsoGlobalSections Y L).hom =
    (homComplexSingleIntegerIsoGlobalSections Y K).hom ≫
      ((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (.up ℤ)).map f := by
  let A : Sheaf AddCommGrpCat Y :=
    (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  let : (IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  let e := NatIso.mapHomologicalComplex (integerConstantHomIsoGlobalSectionsFunctor Y) (.up ℤ)
  have h := CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda_naturality_assoc
    A f (e.hom.app L)
  have h' := congrArg (fun g =>
    (CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda A K).hom ≫ g)
      (e.hom.naturality f)
  exact h.trans (h'.trans (Category.assoc _ _ _).symm)

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

@[simp]
lemma isoHomCongrAddEquiv_apply
    {C : Type*} [Category* C] [Preadditive C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) :
    isoHomCongrAddEquiv eA eB f = eA.inv ≫ f ≫ eB.hom := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle K L n) :
    (kInjectiveDerivedHomAddEquivCohomologyClass K L n).symm
      (CochainComplex.HomComplex.CohomologyClass.mk z) =
    ShiftedHom.map (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
      DerivedCategory.Q := by
  dsimp [kInjectiveDerivedHomAddEquivCohomologyClass,
    isoHomCongrAddEquiv, ShiftedHom.map]
  rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk]
  have h := (DerivedCategory.quotientCompQhIso C).hom.naturality
    (CochainComplex.HomComplex.Cocycle.equivHomShift.symm z)
  dsimp only [Functor.comp_map] at h
  rw [reassoc_of% h]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma kInjectiveDerivedHomAddEquivCohomologyClass_naturality
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (A K L : CochainComplex C ℤ) [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L) (n : ℤ)
    (x : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj K) n) :
    kInjectiveDerivedHomAddEquivCohomologyClass A L n
      (x ≫ (DerivedCategory.Q.map f)⟦n⟧') =
    CochainComplex.HomComplex.postcompClass A f n
      (kInjectiveDerivedHomAddEquivCohomologyClass A K n x) := by
  apply (kInjectiveDerivedHomAddEquivCohomologyClass A L n).symm.injective
  rw [AddEquiv.symm_apply_apply]
  obtain ⟨x, rfl⟩ := (kInjectiveDerivedHomAddEquivCohomologyClass A K n).symm.surjective x
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [AddEquiv.apply_symm_apply, CochainComplex.HomComplex.postcompClass_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyNaturalitySheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- On a K-injective sheaf complex, derived morphisms from the integer
constant sheaf are computed by actual global sections, with no further
replacement complex. -/
def derivedHomAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    ShiftedHom
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)))) (DerivedCategory.Q.obj K) n ≃+
    (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homology n :=
  (kInjectiveDerivedHomAddEquivCohomologyClass _ K n).trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ K n).symm.trans
      (HomologicalComplex.homologyMapIso
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections
          (TopCat.of (ComplexPoint X)) K) n).addCommGroupIsoToAddEquiv)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma derivedHomAddEquivGlobalSectionsKInjective_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) (n : ℤ)
    (x : ShiftedHom
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)))) (DerivedCategory.Q.obj K) n) :
    derivedHomAddEquivGlobalSectionsKInjective X L n
      (x ≫ (DerivedCategory.Q.map f)⟦n⟧') =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
      (derivedHomAddEquivGlobalSectionsKInjective X K n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let A := TopCat.Sheaf.integerConstantSingleComplex Y
  let y := (CochainComplex.HomComplex.homologyAddEquiv A K n).symm
    (kInjectiveDerivedHomAddEquivCohomologyClass A K n x)
  have hH : HomologicalComplex.homologyMap
      (CochainComplex.HomComplex.postcompMap A f) n y =
      (CochainComplex.HomComplex.homologyAddEquiv A L n).symm
        (CochainComplex.HomComplex.postcompClass A f n
          (kInjectiveDerivedHomAddEquivCohomologyClass A K n x)) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv A L n).injective
    rw [CochainComplex.HomComplex.homologyAddEquiv_postcompMap, AddEquiv.apply_symm_apply]
    simp only [AddEquiv.apply_symm_apply]
  have hΓ := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections_naturality Y f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hΓ
  have hΓy := ConcreteCategory.congr_hom hΓ y
  dsimp only [derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [kInjectiveDerivedHomAddEquivCohomologyClass_naturality, ← hH]
  exact hΓy

/-- Hypercohomology of an actual K-injective complex is its global-section
cohomology. This direct form exposes naturality without choosing another
injective resolution. -/
def hypercohomologyAddEquivGlobalSectionsKInjective
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    Hypercohomology X K n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) K).homology n :=
  (hypercohomologyAddEquivDerived X K n).trans
    ((isoHomCongrAddEquiv
      (DerivedCategory.Q.mapIso (constantIntegerSheafComplexIntIsoSingle X))
      (Iso.refl _)).trans
      (derivedHomAddEquivGlobalSectionsKInjective X K n))

set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyAddEquivDerived_naturality
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (f : K ⟶ L) (n : ℤ) (x : Hypercohomology X K n) :
    hypercohomologyAddEquivDerived X L n (hypercohomologyMap X f n x) =
    hypercohomologyAddEquivDerived X K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  simp [hypercohomologyAddEquivDerived, hypercohomologyMap, Hypercohomology,
    Localization.SmallShiftedHom.equiv_comp, ShiftedHom.comp_mk₀]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyAddEquivGlobalSectionsKInjective_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) (n : ℤ)
    (x : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n
      (hypercohomologyMap X f n x) =
    HomologicalComplex.homologyMap
      (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
        (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)).map f) n
      (hypercohomologyAddEquivGlobalSectionsKInjective X K n x) := by
  dsimp only [hypercohomologyAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [hypercohomologyAddEquivDerived_naturality]
  simp only [isoHomCongrAddEquiv_apply, Iso.refl_hom,
    Functor.mapIso_inv, Category.comp_id, ← Category.assoc]
  exact derivedHomAddEquivGlobalSectionsKInjective_naturality X K L f n _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The direct comparison agrees with the existing comparison specialized to
the identity injective resolution. -/
lemma hypercohomologyAddEquivGlobalSectionsKInjective_eq_identityResolution
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective] (n : ℤ) :
    hypercohomologyAddEquivGlobalSectionsKInjective X K n =
      hypercohomologyAddEquivGlobalSectionsOfResolution X K K (𝟙 K) n := by
  ext x
  dsimp only [hypercohomologyAddEquivGlobalSectionsKInjective,
    hypercohomologyAddEquivGlobalSectionsOfResolution,
    derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  simp [isoHomCongrAddEquiv]
  change _ = (inv (𝟙 (_ : AddCommGrpCat))) _
  rw [IsIso.inv_id]
  rfl

end AlgebraicGeometry.ComplexPoint
