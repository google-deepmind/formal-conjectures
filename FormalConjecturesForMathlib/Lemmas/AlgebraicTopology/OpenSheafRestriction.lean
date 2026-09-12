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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.DerivedSheafSupportLocalization
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SheafCohomologyWithSupport
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Exact open restriction with its actual adjunction

The naive open restriction is both a continuous-site direct image (hence
left exact) and isomorphic to topological inverse image (hence right exact).
Its adjunction to open direct image is displayed with the actual restriction
unit used to define sections with support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

set_option backward.isDefEq.respectTransparency false in
instance openSheafRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}) := by
  constructor
  intro J _ _
  let R := U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  let T := sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}
  let : PreservesLimitsOfShape J (R ⋙ T) :=
    inferInstanceAs (PreservesLimitsOfShape J
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj U.isOpenEmbedding.functor.op))
  let : T.Full := inferInstanceAs
    (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).Full
  let : T.Faithful := inferInstanceAs
    (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).Faithful
  exact preservesLimitsOfShape_of_reflects_of_preserves R T

set_option backward.isDefEq.respectTransparency false in
instance openSheafRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}) :=
  preservesFiniteColimits_of_natIso (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})

instance openSheafRestriction_additive :
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).Additive where
  map_add := by intros; rfl

instance openSheafRestriction_isFlasque (F : Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F).IsFlasque where
  epi i := by
    change Epi (F.obj.map _)
    infer_instance

/-- Open restriction preserves quasi-isomorphisms of coefficient complexes. -/
lemma openSheafRestriction_map_quasiIso
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
      (.up ℤ)).map f) := inferInstance

/-- The actual counit of open restriction/direct image. -/
def openSheafRestrictionCounit :
    pushforward AddCommGrpCat.{u} U.inclusion' ⋙
      U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⟶
        𝟭 (Sheaf AddCommGrpCat.{u} (TopCat.of U)) where
  app F := ⟨{
    app V := F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop).op
    naturality V W f := by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map f
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    ext V : 2
    exact (f.hom.naturality _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The open-restriction adjunction with the actual support-defining restriction
as its unit, so later resolution comparisons have a fixed normalization. -/
def openSheafRestrictionAdjunction :
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} ⊣
      pushforward AddCommGrpCat.{u} U.inclusion' :=
  Adjunction.mkOfUnitCounit
    { unit := toOpenRestrictionPushforward X U
      counit := openSheafRestrictionCounit X U
      left_triangle := by
        ext F : 2
        apply CategoryTheory.Sheaf.hom_ext_iff.mpr
        ext V : 2
        change F.obj.map _ ≫ F.obj.map _ = 𝟙 _
        rw [← F.obj.map_comp]
        convert F.obj.map_id _ using 1
        congr 1
      right_triangle := by
        ext F : 2
        apply CategoryTheory.Sheaf.hom_ext_iff.mpr
        ext V : 2
        change F.obj.map _ ≫ F.obj.map _ = 𝟙 _
        rw [← F.obj.map_comp]
        convert F.obj.map_id _ using 1
        congr 1 }

/-- Constant sections on an open subspace map to the restriction of the ambient
constant sheaf, by the sheafification unit itself. -/
def constantToOpenSheafRestriction (A : AddCommGrpCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj A ⟶
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) :=
  ⟨sheafifyLift (Opens.grothendieckTopology (TopCat.of U))
    (Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj A)))
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A)).property⟩

@[reassoc]
lemma toSheafify_constantToOpenSheafRestriction (A : AddCommGrpCat.{u}) :
    toSheafify (Opens.grothendieckTopology (TopCat.of U))
        ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj A) ≫
      (constantToOpenSheafRestriction X U A).hom =
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj A)) :=
  toSheafify_sheafifyLift _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual restriction of ambient constants, followed by the constant/open
comparison, is the support-defining restriction unit. -/
@[reassoc]
lemma constantRestriction_pushforward_constantToOpen (A : AddCommGrpCat.{u}) :
    constantRestriction U.inclusion' A ≫
      (pushforward AddCommGrpCat U.inclusion').map
        (constantToOpenSheafRestriction X U A) =
    (toOpenRestrictionPushforward X U).app
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact ((openRestrictionPushforward X U).obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A)).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    toSheafify_constantRestriction]
  ext V : 2
  change (toSheafify (Opens.grothendieckTopology (TopCat.of U))
    ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj A)).app _ ≫
      (constantToOpenSheafRestriction X U A).hom.app _ = _
  rw [← NatTrans.comp_app, toSheafify_constantToOpenSheafRestriction]
  simpa [toOpenRestrictionPushforward, Topology.IsOpenEmbedding.sheafPullback,
    Functor.sheafPushforwardContinuous, constantSheaf] using ((toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj A)).naturality
      (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V.unop).op)

/-- The inverse constant/open comparison is the adjoint of actual constant
restriction to the subspace. -/
def openSheafRestrictionToConstant (A : AddCommGrpCat.{u}) :
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) ⟶
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj A :=
  ((openSheafRestrictionAdjunction X U).homEquiv _ _).symm
    (constantRestriction U.inclusion' A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma openSheafRestrictionToConstant_constantToOpen (A : AddCommGrpCat.{u}) :
    openSheafRestrictionToConstant X U A ≫ constantToOpenSheafRestriction X U A = 𝟙 _ := by
  apply ((openSheafRestrictionAdjunction X U).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, openSheafRestrictionToConstant,
    Equiv.apply_symm_apply, Adjunction.homEquiv_id]
  exact constantRestriction_pushforward_constantToOpen X U A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma constantToOpen_openSheafRestrictionToConstant (A : AddCommGrpCat.{u}) :
    constantToOpenSheafRestriction X U A ≫ openSheafRestrictionToConstant X U A = 𝟙 _ := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  apply sheafify_hom_ext
  · exact ((constantSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj A).property
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    toSheafify_constantToOpenSheafRestriction]
  dsimp only [openSheafRestrictionToConstant, Adjunction.homEquiv_symm_apply,
    openSheafRestrictionAdjunction, Adjunction.mkOfUnitCounit_counit]
  ext V : 2
  change _ ≫ (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
    (constantRestriction U.inclusion' A)).hom.app V ≫
      ((openSheafRestrictionCounit X U).app _).hom.app V) = _
  rw [← Category.assoc]
  change (toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj A) ≫ (constantRestriction U.inclusion' A).hom).app _ ≫ _ = _
  rw [toSheafify_constantRestriction]
  exact ((toSheafify (Opens.grothendieckTopology (TopCat.of U))
    ((Functor.const (Opens (TopCat.of U))ᵒᵖ).obj A)).naturality
      (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop).op).symm

/-- Constant sheaves commute with open restriction through the explicitly
normalized maps induced by constant sections. -/
def constantOpenSheafRestrictionIso (A : AddCommGrpCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj A ≅
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) where
  hom := constantToOpenSheafRestriction X U A
  inv := openSheafRestrictionToConstant X U A
  hom_inv_id := constantToOpen_openSheafRestrictionToConstant X U A
  inv_hom_id := openSheafRestrictionToConstant_constantToOpen X U A

end TopCat.Sheaf
