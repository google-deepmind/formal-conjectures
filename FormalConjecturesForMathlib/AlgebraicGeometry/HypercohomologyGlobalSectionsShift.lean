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

public import FormalConjecturesForMathlib.Algebra.Homology.HomComplexShiftNaturality
public import FormalConjecturesForMathlib.AlgebraicGeometry.HypercohomologyGlobalSectionsNaturality

/-! # Shift normalization of hypercohomology and global sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace TopCat.Sheaf

variable (Y : TopCat.{0}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
  (s n n' : ℤ) (h : n + s = n')

/-- The canonical three-term map inducing the global-sections homology shift.
Both the additive functor's shift comparison and the usual homology shift are
displayed explicitly. -/
def globalSectionsShiftShortComplex :
    (globalSectionsComplexInt Y (K⟦s⟧)).sc n ⟶
      (globalSectionsComplexInt Y K).sc n' :=
  (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
    ((((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
      (.up ℤ)).commShiftIso s).hom.app K) ≫
    (CochainComplex.shiftShortComplexFunctorIso AddCommGrpCat s n n' (by omega)).hom.app
      (globalSectionsComplexInt Y K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma globalSectionsShiftShortComplex_homologyMap :
    ShortComplex.homologyMap (globalSectionsShiftShortComplex Y K s n n' h) =
    HomologicalComplex.homologyMap
      ((((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (.up ℤ)).commShiftIso s).hom.app K) n ≫
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
        s n n' (by omega)).hom.app (globalSectionsComplexInt Y K) :=
  (ShortComplex.homologyMap_comp _ _).trans
    (congrArg (fun f => HomologicalComplex.homologyMap
      ((((IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).mapHomologicalComplex
        (.up ℤ)).commShiftIso s).hom.app K) n ≫ f)
      (CochainComplex.ShiftSequence.shiftIso_hom_app s n n' (by omega)
        (globalSectionsComplexInt Y K)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma homComplexSingleIntegerGlobalSections_rightUnshift_middle :
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n).map
      (homComplexSingleIntegerIsoGlobalSections Y (K⟦s⟧)).hom ≫
        globalSectionsShiftShortComplex Y K s n n' h).τ₂ =
    (CochainComplex.HomComplex.rightUnshiftShortComplex
      (integerConstantSingleComplex Y) K s n n' h ≫
      (HomologicalComplex.shortComplexFunctor AddCommGrpCat (.up ℤ) n').map
        (homComplexSingleIntegerIsoGlobalSections Y K).hom).τ₂ := by
  subst n'
  ext z
  change (homComplexSingleIntegerIsoGlobalSections Y (K⟦s⟧)).hom.f n z =
    (homComplexSingleIntegerIsoGlobalSections Y K).hom.f (n + s)
      (z.rightUnshift (n + s) rfl)
  exact congrArg
    (fun f : (integerConstantSingleComplex Y).X 0 ⟶ K.X (n + s) =>
      integerConstantHomEquivGlobalSections (K.X (n + s))
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
          ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
            (AddCommGrpCat.of ℤ))).inv ≫ f))
    (CochainComplex.HomComplex.rightUnshift_v_zero
      (integerConstantSingleComplex Y) K s n z).symm

/-- The homology/global-section identification intertwines the exact
target-unshifting maps, including their three-term signs. -/
lemma homComplexSingleIntegerGlobalSections_rightUnshift_homology :
    HomologicalComplex.homologyMap (homComplexSingleIntegerIsoGlobalSections Y (K⟦s⟧)).hom n ≫
      ShortComplex.homologyMap (globalSectionsShiftShortComplex Y K s n n' h) =
    ShortComplex.homologyMap (CochainComplex.HomComplex.rightUnshiftShortComplex
      (integerConstantSingleComplex Y) K s n n' h) ≫
      HomologicalComplex.homologyMap (homComplexSingleIntegerIsoGlobalSections Y K).hom n' :=
  (ShortComplex.homologyMap_comp _ _).symm.trans
    ((ShortComplex.homologyMap_eq_of_middle_eq _ _
      (homComplexSingleIntegerGlobalSections_rightUnshift_middle Y K s n n' h)).trans
      (ShortComplex.homologyMap_comp _ _))

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma kInjectiveDerivedHomAddEquivCohomologyClass_rightUnshift
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (A K : CochainComplex C ℤ) [K.IsKInjective]
    (s n n' : ℤ) (h : n + s = n')
    (x : ShiftedHom (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj (K⟦s⟧)) n) :
    kInjectiveDerivedHomAddEquivCohomologyClass A K n'
      (x.comp ((DerivedCategory.Q.commShiftIso s).hom.app K) (by omega)) =
    CochainComplex.HomComplex.rightUnshiftClass A K s n n' h
      (kInjectiveDerivedHomAddEquivCohomologyClass A (K⟦s⟧) n x) := by
  apply (kInjectiveDerivedHomAddEquivCohomologyClass A K n').symm.injective
  rw [AddEquiv.symm_apply_apply]
  obtain ⟨x, rfl⟩ := (kInjectiveDerivedHomAddEquivCohomologyClass A (K⟦s⟧) n).symm.surjective x
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [AddEquiv.apply_symm_apply, CochainComplex.HomComplex.rightUnshiftClass_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    kInjectiveDerivedHomAddEquivCohomologyClass_symm_mk,
    CochainComplex.HomComplex.equivHomShift_symm_rightUnshift,
    ShiftedHom.map_comp]
  simp [ShiftedHom.map]

variable (X : Over (Spec ↧ℂ))

local instance hypercohomologyShiftSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyAddEquivDerived_rightUnshift
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (s n n' : ℤ) (h : n + s = n')
    (x : Hypercohomology X (K⟦s⟧) n) :
    hypercohomologyAddEquivDerived X K n'
      (x.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (K⟦s⟧) K s from 𝟙 (K⟦s⟧))) (by omega)) =
      (hypercohomologyAddEquivDerived X (K⟦s⟧) n x).comp
        ((DerivedCategory.Q.commShiftIso s).hom.app K) (by omega) := by
  change Localization.SmallShiftedHom.equiv _ DerivedCategory.Q _ =
    ShiftedHom.comp (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q x) _ _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
  congr 1
  simp [ShiftedHom.map]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The direct derived-morphism/global-section comparison commutes with
target unshifting, with the canonical signed homology shift. -/
lemma derivedHomAddEquivGlobalSectionsKInjective_rightUnshift
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (s n n' : ℤ) (h : n + s = n')
    (x : ShiftedHom
      (DerivedCategory.Q.obj (TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)))) (DerivedCategory.Q.obj (K⟦s⟧)) n) :
    derivedHomAddEquivGlobalSectionsKInjective X K n'
      (x.comp ((DerivedCategory.Q.commShiftIso s).hom.app K) (by omega)) =
    ShortComplex.homologyMap (TopCat.Sheaf.globalSectionsShiftShortComplex
      (TopCat.of (ComplexPoint X)) K s n n' h)
      (derivedHomAddEquivGlobalSectionsKInjective X (K⟦s⟧) n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let A := TopCat.Sheaf.integerConstantSingleComplex Y
  let y := (CochainComplex.HomComplex.homologyAddEquiv A (K⟦s⟧) n).symm
    (kInjectiveDerivedHomAddEquivCohomologyClass A (K⟦s⟧) n x)
  have hH : ShortComplex.homologyMap
      (CochainComplex.HomComplex.rightUnshiftShortComplex A K s n n' h) y =
      (CochainComplex.HomComplex.homologyAddEquiv A K n').symm
        (CochainComplex.HomComplex.rightUnshiftClass A K s n n' h
          (kInjectiveDerivedHomAddEquivCohomologyClass A (K⟦s⟧) n x)) := by
    apply (CochainComplex.HomComplex.homologyAddEquiv A K n').injective
    rw [CochainComplex.HomComplex.homologyAddEquiv_rightUnshift,
      AddEquiv.apply_symm_apply]
    simp only [AddEquiv.apply_symm_apply]
  have hΓy := ConcreteCategory.congr_hom
    (TopCat.Sheaf.homComplexSingleIntegerGlobalSections_rightUnshift_homology
      Y K s n n' h) y
  dsimp only [derivedHomAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [kInjectiveDerivedHomAddEquivCohomologyClass_rightUnshift _ _ s n n' h, ← hH]
  exact hΓy.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Hypercohomology unshifting is carried to the canonical, signed
global-section homology shift. The shifted morphism used here is literally
the identity on `K⟦s⟧`, not an independently chosen group equivalence. -/
lemma hypercohomologyAddEquivGlobalSectionsKInjective_rightUnshift
    (K : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [K.IsKInjective]
    (s n n' : ℤ) (h : n + s = n')
    (x : Hypercohomology X (K⟦s⟧) n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X K n'
      (x.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (show ShiftedHom (K⟦s⟧) K s from 𝟙 (K⟦s⟧))) (by omega)) =
    ShortComplex.homologyMap (TopCat.Sheaf.globalSectionsShiftShortComplex
      (TopCat.of (ComplexPoint X)) K s n n' h)
      (hypercohomologyAddEquivGlobalSectionsKInjective X (K⟦s⟧) n x) := by
  dsimp only [hypercohomologyAddEquivGlobalSectionsKInjective, AddEquiv.trans_apply]
  rw [hypercohomologyAddEquivDerived_rightUnshift _ _ s n n' h]
  simp only [isoHomCongrAddEquiv_apply, Iso.refl_hom, Functor.mapIso_inv, Category.comp_id]
  simpa only [ShiftedHom.comp, Category.assoc, Functor.map_id, Category.id_comp] using
    derivedHomAddEquivGlobalSectionsKInjective_rightUnshift X K s n n' h
      (DerivedCategory.Q.map (constantIntegerSheafComplexIntIsoSingle X).inv ≫
        hypercohomologyAddEquivDerived X (K⟦s⟧) n x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The hypercohomology/global-section comparison respects arbitrary
degree-shifted chain maps, in particular the degree-one cone connecting map. -/
lemma hypercohomologyAddEquivGlobalSectionsKInjective_shifted_naturality
    (K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    [K.IsKInjective] [L.IsKInjective]
    (s n n' : ℤ) (h : n + s = n') (f : K ⟶ L⟦s⟧)
    (x : Hypercohomology X K n) :
    hypercohomologyAddEquivGlobalSectionsKInjective X L n'
      (x.comp (Localization.SmallShiftedHom.mk
        (analyticQuasiIsomorphisms X) f) (by omega)) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map f
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)))
        n n' (by omega)
      (hypercohomologyAddEquivGlobalSectionsKInjective X K n x) := by
  have hf : x.comp (Localization.SmallShiftedHom.mk
      (analyticQuasiIsomorphisms X) f) (show s + n = n' by omega) =
      (hypercohomologyMap X f n x).comp
        (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
          (show ShiftedHom (L⟦s⟧) L s from 𝟙 (L⟦s⟧))) (by omega) := by
    apply (hypercohomologyAddEquivDerived X L n').injective
    rw [hypercohomologyAddEquivDerived_rightUnshift _ _ s n n' h,
      hypercohomologyAddEquivDerived_naturality]
    change Localization.SmallShiftedHom.equiv _ DerivedCategory.Q _ = _
    rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
    simp [ShiftedHom.map, ShiftedHom.comp, Category.assoc]
    rfl
  rw [hf, hypercohomologyAddEquivGlobalSectionsKInjective_rightUnshift _ _ s n n' h,
    hypercohomologyAddEquivGlobalSectionsKInjective_naturality,
    TopCat.Sheaf.globalSectionsShiftShortComplex_homologyMap]
  simp only [Functor.shiftMap, ShiftedHom.map, Functor.map_comp,
    AddCommGrpCat.comp_apply]
  rfl

end AlgebraicGeometry.ComplexPoint
