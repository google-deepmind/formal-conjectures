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
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sets.Closeds

/-!
# Concrete sheaf sections with support and their right derived functor

For an open subset `U` of `X`, restriction gives a natural map `F → j_* (F|_U)`.
Its kernel is the sheaf of sections supported on the closed complement of `U`.
This file constructs that additive functor and its right derived functor on the
bounded-below derived category using Mathlib's injective-resolution machinery.

Both the sheaf-valued local cohomology operation, conventionally `RΓ_Z`, and
the abelian-group-valued derived global sections `RΓ_Z` are constructed, with
different source and target categories displayed explicitly.
No dualizing complex or orientation is assumed or constructed. In particular, this
file does not identify Borel--Moore homology with supported cohomology. Comparison
with the project's restriction mapping-cone model, and coherent commutation with
shifts, remain separate theorems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Restrict a sheaf to an open subspace and push it forward again. The pullback
here is the concrete open-embedding pullback, obtained by evaluating on the
corresponding ambient open sets. -/
def openRestrictionPushforward (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  U.isOpenEmbedding.sheafPullback AddCommGrpCat ⋙
    pushforward AddCommGrpCat U.inclusion'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction morphism, functorial in the coefficient sheaf. -/
def toOpenRestrictionPushforward (U : Opens X) :
    𝟭 (Sheaf AddCommGrpCat.{u} X) ⟶ openRestrictionPushforward X U where
  app F := ⟨{
    app V := F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V.unop).op
    naturality V W f := by
      change F.obj.map f ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    ext V : 2
    exact (f.hom.naturality _).symm

/-- The sheaf of sections vanishing on `U`, defined as the kernel of the
coefficient-wise restriction map. -/
def sheafSectionsSupportedOutside (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := kernel ((toOpenRestrictionPushforward X U).app F)
  map f := kernel.map _ _ f ((openRestrictionPushforward X U).map f)
    ((toOpenRestrictionPushforward X U).naturality f).symm
  map_id F := by
    apply (cancel_mono (kernel.ι _)).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp

set_option backward.isDefEq.respectTransparency false in
instance (U : Opens X) : (sheafSectionsSupportedOutside X U).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp [sheafSectionsSupportedOutside, Preadditive.add_comp, Preadditive.comp_add]

/-- Inclusion of supported sections into the original coefficient sheaf. -/
def sheafSectionsSupportedOutsideInclusion (U : Opens X) :
    sheafSectionsSupportedOutside X U ⟶ 𝟭 (Sheaf AddCommGrpCat.{u} X) where
  app F := kernel.ι ((toOpenRestrictionPushforward X U).app F)
  naturality F G f := by simp [sheafSectionsSupportedOutside]

@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideInclusion_restriction (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsSupportedOutsideInclusion X U).app F ≫
      (toOpenRestrictionPushforward X U).app F = 0 :=
  kernel.condition _

/-- A morphism of sheaves whose restriction to `U` is zero factors canonically
through the sheaf of sections supported outside `U`. -/
def liftSheafSectionsSupportedOutside (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0) :
    F ⟶ (sheafSectionsSupportedOutside X U).obj G :=
  kernel.lift _ f hf

@[reassoc (attr := simp)]
lemma liftSheafSectionsSupportedOutside_inclusion (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0) :
    liftSheafSectionsSupportedOutside X U f hf ≫
      (sheafSectionsSupportedOutsideInclusion X U).app G = f :=
  kernel.lift_ι _ _ _

/-- Uniqueness in the universal property of supported sections. -/
lemma liftSheafSectionsSupportedOutside_unique (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0)
    (g : F ⟶ (sheafSectionsSupportedOutside X U).obj G)
    (hg : g ≫ (sheafSectionsSupportedOutsideInclusion X U).app G = f) :
    g = liftSheafSectionsSupportedOutside X U f hf :=
  (cancel_mono (kernel.ι _)).1 (hg.trans (kernel.lift_ι _ _ _).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On every ambient open set, supported sections are exactly the kernel of
restriction to its intersection with `U`. This is the canonical kernel
comparison, not a supplied equivalence. -/
def sheafSectionsSupportedOutsideOnOpenIso (U V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ≅
      kernel (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) := by
  let ev : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op V)
  letI : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI : PreservesLimitsOfShape WalkingParallelPair ev :=
    comp_preservesLimitsOfShape
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  exact PreservesKernel.iso ev ((toOpenRestrictionPushforward X U).app F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The kernel comparison preserves the actual inclusion of supported sections
into all sections. -/
@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideOnOpenIso_hom_ι (U V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsSupportedOutsideOnOpenIso X U V F).hom ≫
      kernel.ι (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) =
        ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) := by
  let ev : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op V)
  let _ : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesLimitsOfShape WalkingParallelPair ev :=
    comp_preservesLimitsOfShape
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  change (PreservesKernel.iso ev ((toOpenRestrictionPushforward X U).app F)).hom ≫
    _ = _
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι ((toOpenRestrictionPushforward X U).app F) ev

/-- Restriction to the empty open subspace and pushforward gives the zero sheaf. -/
lemma isZero_openRestrictionPushforward_bot (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero ((openRestrictionPushforward X ⊥).obj F) := by
  exact (pushforward AddCommGrpCat (⊥ : Opens X).inclusion').map_isZero
    ((isZero_iff_stalkFunctor_obj_isZero _).2 fun x => False.elim x.property)

instance (F : Sheaf AddCommGrpCat.{u} X) :
    IsIso ((sheafSectionsSupportedOutsideInclusion X ⊥).app F) := by
  change IsIso (kernel.ι ((toOpenRestrictionPushforward X ⊥).app F))
  rw [(isZero_openRestrictionPushforward_bot X F).eq_zero_of_tgt
    ((toOpenRestrictionPushforward X ⊥).app F)]
  infer_instance

/-- With no restriction imposed, the support-sheaf inclusion is canonically an
isomorphism with the original coefficient sheaf. -/
def sheafSectionsSupportedOutsideBotIso :
    sheafSectionsSupportedOutside X ⊥ ≅ 𝟭 (Sheaf AddCommGrpCat.{u} X) :=
  NatIso.ofComponents
    (fun F => asIso ((sheafSectionsSupportedOutsideInclusion X ⊥).app F))
    (fun f => (sheafSectionsSupportedOutsideInclusion X ⊥).naturality f)

/-- The sheaf-valued sections-with-support functor for a closed support. -/
def sheafSectionsWithClosedSupport (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  sheafSectionsSupportedOutside X Z.compl

instance (Z : Closeds X) : (sheafSectionsWithClosedSupport X Z).Additive :=
  inferInstanceAs (sheafSectionsSupportedOutside X Z.compl).Additive

/-- Sections supported on the whole space are all sections, through the actual
support-forgetting inclusion. -/
def sheafSectionsWithClosedSupportTopIso :
    sheafSectionsWithClosedSupport X ⊤ ≅ 𝟭 (Sheaf AddCommGrpCat.{u} X) := by
  have h : (⊤ : Closeds X).compl = ⊥ := by ext; simp
  simpa only [sheafSectionsWithClosedSupport, h] using
    sheafSectionsSupportedOutsideBotIso X

/-- Global sections supported in a closed subset, obtained by evaluating the
concrete support sheaf on the whole ambient space. -/
def closedSupportSections (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafSectionsWithClosedSupport X Z ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op ⊤)

instance (Z : Closeds X) : (closedSupportSections X Z).Additive where
  map_add {F G} f g :=
    congrArg (fun h : (sheafSectionsWithClosedSupport X Z).obj F ⟶
        (sheafSectionsWithClosedSupport X Z).obj G => h.hom.app (op ⊤))
      ((sheafSectionsWithClosedSupport X Z).map_add (f := f) (g := g))

local instance supportSheafHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance supportGroupsHasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

/-- The genuine right derived sheaf sections-with-support functor on bounded-below
complexes. Enough injectives is furnished by the Grothendieck abelian category of
abelian sheaves, not supplied as mathematical data. -/
def derivedSheafSectionsWithClosedSupport (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlus

/-- The canonical comparison from termwise sections with support to their derived
functor. -/
def derivedSheafSectionsWithClosedSupportUnit (Z : Closeds X) :
    (sheafSectionsWithClosedSupport X Z).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedSheafSectionsWithClosedSupport X Z :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlusUnit

/-- This construction satisfies Mathlib's universal property of a right derived
functor; it is not merely a named candidate endofunctor. -/
instance derivedSheafSectionsWithClosedSupport_isRightDerivedFunctor (Z : Closeds X) :
    (derivedSheafSectionsWithClosedSupport X Z).IsRightDerivedFunctor
      (derivedSheafSectionsWithClosedSupportUnit X Z)
      (HomotopyCategory.Plus.quasiIso (Sheaf AddCommGrpCat.{u} X)) := by
  dsimp only [derivedSheafSectionsWithClosedSupport,
    derivedSheafSectionsWithClosedSupportUnit]
  infer_instance

/-- A bounded-below complex of injective sheaves computes sheaf-valued derived
sections with support by applying the concrete support functor termwise. -/
instance derivedSheafSectionsWithClosedSupportUnit_isIso_injectiveComplex (Z : Closeds X)
    (K : HomotopyCategory.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    IsIso ((derivedSheafSectionsWithClosedSupportUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj K)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    ((sheafSectionsWithClosedSupport X Z).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
        (derivedSheafSectionsWithClosedSupportUnit X Z) K

/-- The group-valued derived sections-with-support functor `RΓ_Z` on
bounded-below complexes. This is derived from the actual functor of global
sections vanishing on the complement. -/
def derivedClosedSupportSections (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  (closedSupportSections X Z).rightDerivedFunctorPlus

/-- The canonical unit defining group-valued derived sections with support. -/
def derivedClosedSupportSectionsUnit (Z : Closeds X) :
    (closedSupportSections X Z).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedClosedSupportSections X Z :=
  (closedSupportSections X Z).rightDerivedFunctorPlusUnit

/-- Group-valued supported sections satisfy the universal property of their
right derived functor. -/
instance derivedClosedSupportSections_isRightDerivedFunctor (Z : Closeds X) :
    (derivedClosedSupportSections X Z).IsRightDerivedFunctor
      (derivedClosedSupportSectionsUnit X Z)
      (HomotopyCategory.Plus.quasiIso (Sheaf AddCommGrpCat.{u} X)) := by
  dsimp only [derivedClosedSupportSections, derivedClosedSupportSectionsUnit]
  infer_instance

/-- A bounded-below complex of injective sheaves computes group-valued derived
sections with support by taking supported global sections termwise. -/
instance derivedClosedSupportSectionsUnit_isIso_injectiveComplex (Z : Closeds X)
    (K : HomotopyCategory.Plus (InjectiveObject (Sheaf AddCommGrpCat.{u} X))) :
    IsIso ((derivedClosedSupportSectionsUnit X Z).app
      ((InjectiveObject.ι (Sheaf AddCommGrpCat.{u} X)).mapHomotopyCategoryPlus.obj K)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
    ((closedSupportSections X Z).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
        (derivedClosedSupportSectionsUnit X Z) K

end TopCat.Sheaf
