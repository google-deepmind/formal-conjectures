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

public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.MappingConeConnectingNaturality
public import FormalConjecturesForMathlib.AlgebraicGeometry.DerivedSupportRationalConeComparison
public import FormalConjecturesForMathlib.AlgebraicGeometry.HypercohomologyGlobalSectionsShift

/-! # Support-forgetting in the actual rational injective model -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

local instance rationalConeForgetSheafDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

instance ambientRationalInjectiveComplex_isKInjective :
    (ambientRationalInjectiveComplex X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Ordinary rational cohomology computed by the actual ambient rational
injective resolution. This has the ordinary augmentation normalization. -/
def rationalCohomologyAddEquivAmbientInjectiveHomology (n : ℤ) :
    FieldCohomology ℚ X n ≃+
      (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X))
        (ambientRationalInjectiveComplex X)).homology n := by
  let e : FieldCohomology ℚ X n ≃+
      Hypercohomology X (ambientRationalInjectiveComplex X) n :=
    { toEquiv := Localization.SmallShiftedHom.postcompEquiv
        (ambientRationalInjectiveAugmentation X)
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)
      map_add' α β := (hypercohomologyMap X
        (ambientRationalInjectiveAugmentation X) n).map_add α β }
  exact e.trans (hypercohomologyAddEquivGlobalSectionsKInjective X _ n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyAddEquivDerived_comp_shifted
    {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (s n n' : ℤ) (h : s + n = n') (g : K ⟶ L⟦s⟧)
    (x : Hypercohomology X K n) :
    hypercohomologyAddEquivDerived X L n'
      (x.comp (Localization.SmallShiftedHom.mk
        (analyticQuasiIsomorphisms X) g) h) =
    (hypercohomologyAddEquivDerived X K n x).comp
      (ShiftedHom.map g DerivedCategory.Q) h := by
  change Localization.SmallShiftedHom.equiv _ DerivedCategory.Q _ = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma hypercohomologyMap_comp_shifted
    {K L K' L' : CochainComplex (AnalyticAdditiveSheaf X) ℤ}
    (s n n' : ℤ) (h : s + n = n')
    (a : K ⟶ K') (b : L ⟶ L') (g : K ⟶ L⟦s⟧) (g' : K' ⟶ L'⟦s⟧)
    (hab : a ≫ g' = g ≫ b⟦s⟧') (x : Hypercohomology X K n) :
    hypercohomologyMap X b n'
      (x.comp (Localization.SmallShiftedHom.mk
        (analyticQuasiIsomorphisms X) g) h) =
    (hypercohomologyMap X a n x).comp
      (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X) g') h := by
  apply (hypercohomologyAddEquivDerived X L' n').injective
  rw [hypercohomologyAddEquivDerived_naturality,
    hypercohomologyAddEquivDerived_comp_shifted,
    hypercohomologyAddEquivDerived_comp_shifted,
    hypercohomologyAddEquivDerived_naturality]
  exact ShiftedHom.comp_commSq s n n' h _ _ _ _
    (ShiftedHom.map_commSq s a b g g' hab DerivedCategory.Q) _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original support-forgetting map, after replacing the ambient
constant sheaf by its actual injective resolution, is the actual cone
connecting homology map. -/
lemma rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
      (forgetSupport X Z n x) =
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftMap
      (ShiftedHom.map
        (CochainComplex.mappingCone.triangle
          (ambientRationalInjectiveRestriction X Z hZ)).mor₃
        ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
          (TopCat.of (ComplexPoint X))).mapHomologicalComplex (.up ℤ)))
      (n - 1) n (by omega)
      (rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x) := by
  change hypercohomologyAddEquivGlobalSectionsKInjective X _ n
    (hypercohomologyMap X (ambientRationalInjectiveAugmentation X) n
      (x.comp (Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (CochainComplex.mappingCone.triangle
          (rationalRestrictionComplexInt X Z)).mor₃) (by omega))) = _
  exact (congrArg (hypercohomologyAddEquivGlobalSectionsKInjective X
    (ambientRationalInjectiveComplex X) n)
    (hypercohomologyMap_comp_shifted _ 1 (n - 1) n (by omega)
    (rationalSupportConeToAmbientInjectiveCone X Z hZ) _ _ _
    (rationalSupportConeToAmbientInjectiveCone_connecting X Z hZ) x)).trans
    (hypercohomologyAddEquivGlobalSectionsKInjective_shifted_naturality
      X
        (CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ))
        (ambientRationalInjectiveComplex X) 1 (n - 1) n (by omega) _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- The normalized support equivalence intertwines the existing
`forgetSupport` with the actual inclusion of supported injective sections.
No compatibility or choice of a sign is supplied as an input. -/
lemma rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ)
    (x : RationalCohomologyWithSupport X Z n) :
    rationalCohomologyAddEquivAmbientInjectiveHomology X n
      (forgetSupport X Z n x) =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) ⟨Zᶜ, hZ.isOpen_compl⟩ ⊤
        (ambientRationalInjectiveComplex X)).f n
      (rationalSupportAddEquivSupportedInjectiveHomology X Z hZ n x) := by
  let Y := TopCat.of (ComplexPoint X)
  let U : Opens Y := ⟨Zᶜ, hZ.isOpen_compl⟩
  let Γ := TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤
    (ambientRationalInjectiveComplex X)
  let b := ambientRationalInjectiveRestriction X Z hZ
  let c := actualSupportConeToAmbientInjectiveGlobalCone X Z hZ
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso b Γ
  let y := rationalSupportAddEquivAmbientInjectiveConeGlobalSections X Z hZ n x
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
  have hc : HomologicalComplex.homologyMap c (n - 1) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃ (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) := by
    change (H.shift (n - 1)).map c ≫ _ = _
    rw [← Functor.shiftMap_comp', actualSupportConeToAmbientInjectiveGlobalCone_connecting]
  have hc' : inv (HomologicalComplex.homologyMap c (n - 1)) ≫
      H.shiftMap (CochainComplex.mappingCone.triangle S.g).mor₃ (n - 1) n (by omega) =
      H.shiftMap (CochainComplex.mappingCone.triangle
        ((Γ.mapHomologicalComplex (.up ℤ)).map b)).mor₃ (n - 1) n (by omega) := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  have hl := CochainComplex.mappingCocone.inv_homologyMap_shiftedLiftShortComplex_connecting
    S (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact Y U ⊤ _)
    (n - 1) n (by omega)
  have he := CochainComplex.mappingCone.mapHomologicalComplexIso_homology_connecting
    b Γ (n - 1) n (by omega)
  rw [rationalCohomologyAddEquivAmbientInjectiveHomology_forgetSupport_cone]
  change H.shiftMap (ShiftedHom.map (CochainComplex.mappingCone.triangle b).mor₃
      (Γ.mapHomologicalComplex (.up ℤ))) (n - 1) n (by omega) y =
    HomologicalComplex.homologyMap S.f n
      (-(((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y)))))
  rw [map_neg]
  have hly := ConcreteCategory.congr_hom hl
    ((inv (HomologicalComplex.homologyMap c (n - 1)))
      (HomologicalComplex.homologyMap e.hom (n - 1) y))
  change -(HomologicalComplex.homologyMap S.f n
      (((H.shiftIso 1 (n - 1) n (by omega)).hom.app S.X₁)
        ((inv (HomologicalComplex.homologyMap
          (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)))
          ((inv (HomologicalComplex.homologyMap c (n - 1)))
            (HomologicalComplex.homologyMap e.hom (n - 1) y))))) = _ at hly
  rw [hly]
  exact (ConcreteCategory.congr_hom he y).symm.trans
    (ConcreteCategory.congr_hom hc' (HomologicalComplex.homologyMap e.hom (n - 1) y)).symm

end AlgebraicGeometry.ComplexPoint
