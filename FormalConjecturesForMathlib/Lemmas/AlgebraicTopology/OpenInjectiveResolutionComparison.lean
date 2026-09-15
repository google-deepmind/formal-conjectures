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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.OpenInjectiveResolutionComparison

/-!
# Comparing an ambient resolution with a resolution on an open subspace

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.OpenInjectiveResolutionComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

variable {A K I : CochainComplex C ℕ} (a : A ⟶ K) [Mono a] [QuasiIso a]
  (r : A ⟶ I) (hI : ∀ n, Injective (I.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma comp_liftToInjectiveNat : a ≫ liftToInjectiveNat a r hI = r := by
  let := mono_extendMap_nat a
  let : CochainComplex.IsStrictlyGE (A.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (I.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  apply (ComplexShape.embeddingUpNat.extendFunctor C).map_injective
  rw [Functor.map_comp]
  dsimp only [liftToInjectiveNat]
  rw [Functor.map_preimage]
  exact comp_liftToInjective
    (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat)
    (injective_extend_nat I hI)

lemma liftToInjectiveNat_quasiIso [QuasiIso r] : QuasiIso (liftToInjectiveNat a r hI) := by
  have : QuasiIso (a ≫ liftToInjectiveNat a r hI) := by
    rw [comp_liftToInjectiveNat]
    infer_instance
  exact quasiIso_of_comp_left a _

end CochainComplex

namespace TopCat.Sheaf

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

@[reassoc (attr := simp)]
lemma restrictedAmbientAugmentation_comp_comparison :
    restrictedAmbientConstantAugmentation X U A ≫
      restrictedAmbientToOpenResolution X U A = (openConstantInjectiveResolution X U A).ι :=
  CochainComplex.comp_liftToInjectiveNat _ _ _

lemma restrictedAmbientToOpenResolution_quasiIso :
    QuasiIso (restrictedAmbientToOpenResolution X U A) := by
  let : QuasiIso (openConstantInjectiveResolution X U A).ι :=
    (openConstantInjectiveResolution X U A).quasiIso
  exact CochainComplex.liftToInjectiveNat_quasiIso _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Strict normalization: the independently resolved restriction extends
the actual restriction map of constant sheaves. -/
@[reassoc]
lemma ambientAugmentation_comp_openResolution :
    (ambientConstantInjectiveResolution X A).ι ≫ ambientToOpenInjectiveResolution X U A =
      (CochainComplex.single₀ _).map (constantRestriction U.inclusion' A) ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (pushforward AddCommGrpCat U.inclusion') (.up ℕ) 0).inv.app _ ≫
        ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
          (openConstantInjectiveResolution X U A).ι := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change (ambientConstantInjectiveResolution X A).ι.f 0 ≫
        ((toOpenRestrictionPushforward X U).app _ ≫
          (pushforward AddCommGrpCat U.inclusion').map
            ((restrictedAmbientToOpenResolution X U A).f 0)) =
      constantRestriction U.inclusion' A ≫
        (pushforward AddCommGrpCat U.inclusion').map
          ((openConstantInjectiveResolution X U A).ι.f 0)
    have hnat := (toOpenRestrictionPushforward X U).naturality
      ((ambientConstantInjectiveResolution X A).ι.f 0)
    dsimp only [Functor.id_map] at hnat
    rw [← Category.assoc, hnat]
    change ((toOpenRestrictionPushforward X U).app
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) ≫ _) ≫ _ = _
    rw [← constantRestriction_pushforward_constantToOpen]
    dsimp only [openRestrictionPushforward, Functor.comp_map]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have h := HomologicalComplex.congr_hom
      (restrictedAmbientAugmentation_comp_comparison X U A) 0
    change (constantOpenSheafRestrictionIso X U A).hom ≫
        (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
          ((ambientConstantInjectiveResolution X A).ι.f 0) ≫
        (restrictedAmbientToOpenResolution X U A).f 0 =
      (openConstantInjectiveResolution X U A).ι.f 0 at h
    dsimp only [constantOpenSheafRestrictionIso] at h
    exact congrArg (fun f => constantRestriction U.inclusion' A ≫
      (pushforward AddCommGrpCat U.inclusion').map f) h
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ (n + 1) (by omega)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- The comparison remains a quasi-isomorphism after global sections: on the
open subspace both actual resolutions are termwise flasque. No exactness of
open direct image on arbitrary complexes is asserted. -/
theorem globalRestrictedAmbientToOpenResolution_quasiIso :
    QuasiIso (globalRestrictedAmbientToOpenResolution X U A) := by
  change QuasiIso
    (((IsFlasque.BoundedBelowComplex.globalSectionsFunctor (TopCat.of U)).mapHomologicalComplex
      (.up ℕ)).map (restrictedAmbientToOpenResolution X U A))
  let : QuasiIso (restrictedAmbientToOpenResolution X U A) :=
    restrictedAmbientToOpenResolution_quasiIso X U A
  apply AlgebraicGeometry.ComplexPoint.globalSectionsNat_map_quasiIso
  · exact restrictedAmbientConstantResolution_isFlasque X U A
  · exact fun n => @injective_isFlasque _ _ ((openConstantInjectiveResolution X U A).injective n)

end TopCat.Sheaf
