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

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sheaves.Functors

import FormalConjecturesForMathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Abelian

/-!
# Sheaf cohomology with closed and compact supports

For a closed subset `Z` of a topological space `X`, let `A_Z` be the pushforward of the
constant integer sheaf on `Z`. Cohomology with support in `Z` is `Extⁿ(A_Z, F)`, in the
category of abelian sheaves on `X`. Compactly supported cohomology is the colimit of these
groups over compact closed subsets. Closedness is explicit, so the construction does not
require a separation or local compactness assumption on `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

/-- Compact closed subsets, ordered by inclusion. Compactness does not imply closedness
unless a suitable separation assumption is available. -/
abbrev TopologicalSpace.CompactCloseds (X : Type u) [TopologicalSpace X] :=
  {K : Closeds X // IsCompact (K : Set X)}

namespace TopologicalSpace.CompactCloseds

variable (X : Type u) [TopologicalSpace X]

instance : Nonempty (CompactCloseds X) := ⟨⟨⊥, isCompact_empty⟩⟩

instance : IsFiltered (CompactCloseds X) where
  cocone_objs K L :=
    ⟨⟨K.1 ⊔ L.1, K.2.union L.2⟩,
      homOfLE (show K.1 ≤ K.1 ⊔ L.1 from le_sup_left),
      homOfLE (show L.1 ≤ K.1 ⊔ L.1 from le_sup_right), trivial⟩
  cocone_maps _ L _ _ := ⟨L, 𝟙 _, Subsingleton.elim _ _⟩

/-- Forget the compactness proof of a compact closed subset. -/
def inclusion : CompactCloseds X ⥤ Closeds X where
  obj K := K.1
  map f := homOfLE (leOfHom f)

/-- The whole space as a compact closed support. -/
def univ [CompactSpace X] : CompactCloseds X := ⟨⊤, isCompact_univ⟩

/-- On a compact space, the whole space is a terminal support. -/
def isTerminalUniv [CompactSpace X] : IsTerminal (univ X) :=
  IsTerminal.ofUniqueHom (fun K => homOfLE (show K.1 ≤ ⊤ from le_top))
    (fun _ _ => Subsingleton.elim _ _)

end TopologicalSpace.CompactCloseds

namespace TopCat.Sheaf

open _root_.Opens

@[inherit_doc grothendieckTopology]
notation "𝓖[" X "]" => grothendieckTopology X

@[inherit_doc constantSheaf]
notation3 "𝓒[" Y " ; " A "]" => (constantSheaf 𝓖[Y] AddCommGrpCat).obj A

/-- Constant sheaves restrict along a continuous map. -/
def constantRestriction {X Y : TopCat.{u}} (f : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    𝓒[Y; A] ⟶ (pushforward _ f).obj 𝓒[X; A] :=
  ⟨sheafifyLift 𝓖[Y] (Functor.whiskerLeft (Opens.map f).op (toSheafify 𝓖[X]
    ((Functor.const (Opens X)ᵒᵖ).obj A)))
    ((pushforward AddCommGrpCat f).obj
      ((constantSheaf 𝓖[X] _).obj A)).property⟩

@[reassoc]
lemma toSheafify_constantRestriction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A : AddCommGrpCat.{u}) :
    toSheafify 𝓖[Y] ((Functor.const (Opens Y)ᵒᵖ).obj A) ≫
        (constantRestriction f A).hom =
      Functor.whiskerLeft (Opens.map f).op
        (toSheafify 𝓖[X] ((Functor.const (Opens X)ᵒᵖ).obj A)) :=
  toSheafify_sheafifyLift _ _ _

@[simp]
lemma constantRestriction_id (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    constantRestriction (𝟙 X) A = 𝟙 _ := by
  ext1
  apply sheafify_hom_ext
  · exact ((constantSheaf 𝓖[X] AddCommGrpCat).obj A).property
  · exact (toSheafify_constantRestriction (𝟙 X) A).trans (by rfl)

lemma constantRestriction_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : AddCommGrpCat.{u}) :
    constantRestriction (f ≫ g) A =
      constantRestriction g A ≫ (pushforward AddCommGrpCat g).map (constantRestriction f A) := by
  ext1
  apply sheafify_hom_ext
  · exact ((pushforward AddCommGrpCat (f ≫ g)).obj
      ((constantSheaf 𝓖[X] AddCommGrpCat).obj A)).property
  · change _ = _ ≫ (constantRestriction g A).hom ≫
      Functor.whiskerLeft (Opens.map g).op (constantRestriction f A).hom
    rw [toSheafify_constantRestriction]
    erw [← Category.assoc, toSheafify_constantRestriction]
    apply NatTrans.ext
    funext U
    exact (NatTrans.congr_app (toSheafify_constantRestriction f A)
      ((Opens.map g).op.obj U)).symm

variable (X : TopCat.{u})

/-- The inclusion of a closed subspace. -/
def closedInclusion (Z : Closeds X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The integer sheaf on a closed subspace, pushed forward to the ambient space. -/
def supportIntegerSheaf (Z : Closeds X) :
    CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} :=
  (pushforward AddCommGrpCat (closedInclusion X Z)).obj
    ((constantSheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- Restriction of the ambient integer sheaf to a closed support. -/
def integerToSupport (Z : Closeds X) :
    (constantSheaf 𝓖[X] AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ supportIntegerSheaf X Z :=
  constantRestriction (closedInclusion X Z) _

/-- Restriction from a larger closed support to a smaller one. -/
def supportIntegerSheafMap {Z W : Closeds X} (h : Z ≤ W) :
    supportIntegerSheaf X W ⟶ supportIntegerSheaf X Z :=
  (pushforward AddCommGrpCat (closedInclusion X W)).map
    (constantRestriction
      (TopCat.ofHom ⟨fun z : Z => (⟨z.1, h z.2⟩ : W),
        continuous_subtype_val.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ)))

@[simp]
lemma supportIntegerSheafMap_refl (Z : Closeds X) :
    supportIntegerSheafMap X (le_refl Z) = 𝟙 _ := by
  change (pushforward AddCommGrpCat (closedInclusion X Z)).map
    (constantRestriction (𝟙 (TopCat.of Z)) _) = _
  rw [constantRestriction_id]
  rfl

lemma supportIntegerSheafMap_trans {Z W V : Closeds X} (hZW : Z ≤ W) (hWV : W ≤ V) :
    supportIntegerSheafMap X (hZW.trans hWV) =
      supportIntegerSheafMap X hWV ≫ supportIntegerSheafMap X hZW := by
  let f : TopCat.of Z ⟶ TopCat.of W :=
    TopCat.ofHom ⟨fun z => ⟨z.1, hZW z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let g : TopCat.of W ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, continuous_subtype_val.subtype_mk _⟩
  change (pushforward AddCommGrpCat (closedInclusion X V)).map
    (constantRestriction (f ≫ g) _) = _
  rw [constantRestriction_comp]
  rfl

@[reassoc (attr := simp)]
lemma integerToSupport_map {Z W : Closeds X} (h : Z ≤ W) :
    integerToSupport X W ≫ supportIntegerSheafMap X h = integerToSupport X Z :=
  (constantRestriction_comp (TopCat.ofHom ⟨fun z : Z => (⟨z.1, h z.2⟩ : W),
    continuous_subtype_val.subtype_mk _⟩) (closedInclusion X W) _).symm

/-- The contravariant diagram of integer sheaves on closed supports. -/
def supportIntegerSheafFunctor :
    (Closeds X)ᵒᵖ ⥤
      CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} where
  obj Z := supportIntegerSheaf X Z.unop
  map f := supportIntegerSheafMap X (leOfHom f.unop)
  map_id Z := supportIntegerSheafMap_refl X Z.unop
  map_comp f g := supportIntegerSheafMap_trans X (leOfHom g.unop) (leOfHom f.unop)

/-- The integer sheaf supported on the whole space is the ordinary integer sheaf. -/
def supportIntegerSheafTopIso :
    (constantSheaf 𝓖[X] AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ≅ supportIntegerSheaf X ⊤ where
  hom := integerToSupport X ⊤
  inv := (pushforward AddCommGrpCat (closedInclusion X ⊤)).map
    (constantRestriction
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ)))
  hom_inv_id :=
   (constantRestriction_comp
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (closedInclusion X ⊤) _).symm.trans
      (constantRestriction_id X _)
  inv_hom_id := by
    have h := (constantRestriction_comp (closedInclusion X ⊤)
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ))).symm.trans
      (constantRestriction_id (TopCat.of (⊤ : Closeds X)) _)
    exact congrArg ((pushforward AddCommGrpCat (closedInclusion X ⊤)).map) h

/-- The integer sheaf supported on the empty subset is zero. -/
lemma isZero_supportIntegerSheaf_bot : IsZero (supportIntegerSheaf X ⊥) := by
  apply (pushforward AddCommGrpCat (closedInclusion X ⊥)).map_isZero
  apply (isZero_iff_stalkFunctor_obj_isZero _).2
  exact fun x ↦ False.elim x.property

local instance :
    HasExt.{u} (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})

/-- Sheaf cohomology with support in a closed subset, defined using Mathlib's Ext. -/
abbrev cohomologyWithSupport (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :=
  Ext (supportIntegerSheaf X Z) F n

instance (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGroup (cohomologyWithSupport X Z F n) :=
  inferInstanceAs (AddCommGroup (Ext (supportIntegerSheaf X Z) F n))

/-- In degree zero, supported cohomology consists of morphisms from the support integer sheaf. -/
def cohomologyWithSupportZeroEquiv (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) :
    cohomologyWithSupport X Z F 0 ≃+ (supportIntegerSheaf X Z ⟶ F) :=
  Ext.addEquiv₀

instance (Z : Closeds X) (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})
    [Injective F] (n : ℕ) : Subsingleton (cohomologyWithSupport X Z F (n + 1)) :=
  Ext.subsingleton_of_injective _ _ n

/-- Cohomology with closed support, functorial in both support and coefficients. -/
def cohomologyWithSupportFunctor (n : ℕ) :
    Closeds X ⥤ CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (supportIntegerSheafFunctor X).rightOp ⋙ extFunctor n

/-- Cohomology with empty support vanishes in every degree. -/
lemma isZero_cohomologyWithSupport_bot
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    IsZero (AddCommGrpCat.of (cohomologyWithSupport X ⊥ F n)) :=
  ((extFunctor n).flip.obj F).map_isZero (isZero_supportIntegerSheaf_bot X).op

/-- Forget a closed support. -/
def forgetClosedSupport (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    cohomologyWithSupport X Z F n →+ CategoryTheory.Sheaf.H.{u, u} F n :=
  (Ext.mk₀ (integerToSupport X Z)).precomp F (zero_add n)

/-- Forgetting whole-space support identifies supported cohomology with Mathlib's cohomology. -/
def cohomologyWithSupportTopIso
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.of (cohomologyWithSupport X ⊤ F n) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u, u} F n) :=
  ((extFunctor n).mapIso (supportIntegerSheafTopIso X).op).app F

@[simp]
lemma cohomologyWithSupportTopIso_hom
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (cohomologyWithSupportTopIso X F n).hom =
      AddCommGrpCat.ofHom (forgetClosedSupport X ⊤ F n) := rfl

@[reassoc]
lemma forgetClosedSupport_naturality (Z : Closeds X)
    {F G : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}}
    (f : F ⟶ G) (n : ℕ) :
    ((cohomologyWithSupportFunctor X n).obj Z).map f ≫
        AddCommGrpCat.ofHom (forgetClosedSupport X Z G n) =
      AddCommGrpCat.ofHom (forgetClosedSupport X Z F n) ≫
        (CategoryTheory.Sheaf.functorH 𝓖[X] n).map f :=
  ((extFunctor n).map (integerToSupport X Z).op).naturality f

@[simp]
lemma forgetClosedSupport_enlarge {Z W : Closeds X} (h : Z ≤ W)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})
    (n : ℕ) (α : cohomologyWithSupport X Z F n) :
    forgetClosedSupport X W F n
      (((cohomologyWithSupportFunctor X n).map (homOfLE h)).app F α) =
        forgetClosedSupport X Z F n α := by
  change (Ext.mk₀ (integerToSupport X W)).comp
    ((Ext.mk₀ (supportIntegerSheafMap X h)).comp α (zero_add n)) (zero_add n) = _
  rw [Ext.mk₀_comp_mk₀_assoc, integerToSupport_map]
  rfl

/-- The diagram of cohomology groups indexed by compact closed supports. -/
def compactSupportDiagram
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    CompactCloseds X ⥤ AddCommGrpCat.{u} :=
  ((CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip).obj F

/-- Compactly supported cohomology, functorial in the coefficient sheaf. -/
def compactlySupportedCohomologyFunctor (n : ℕ) :
    CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip ⋙ colim

/-- Compactly supported sheaf cohomology as a filtered colimit of Ext groups. -/
abbrev compactlySupportedCohomology
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.{u} :=
  (compactlySupportedCohomologyFunctor X n).obj F

/-- A class with specified compact closed support defines a compactly supported class. -/
def toCompactlySupportedCohomology (K : CompactCloseds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.of (cohomologyWithSupport X K.1 F n) ⟶
      compactlySupportedCohomology X F n :=
  colimit.ι (compactSupportDiagram X F n) K

@[reassoc (attr := simp)]
lemma toCompactlySupportedCohomology_enlarge {K L : CompactCloseds X} (h : K ≤ L)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (compactSupportDiagram X F n).map (homOfLE h) ≫
        toCompactlySupportedCohomology X L F n =
      toCompactlySupportedCohomology X K F n :=
  colimit.w _ _

/-- Higher compactly supported cohomology vanishes on injective coefficient sheaves. -/
lemma isZero_compactlySupportedCohomology_injective
    (F :
    CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) [Injective F] (n : ℕ) :
    IsZero (compactlySupportedCohomology X F (n + 1)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply colimit.hom_ext
  intro K
  have h : IsZero ((compactSupportDiagram X F (n + 1)).obj K) :=
    AddCommGrpCat.isZero_iff_subsingleton.2
      (Ext.subsingleton_of_injective _ F n)
  exact h.eq_of_src _ _

/-- Forgetting each compact support gives a cocone to ordinary sheaf cohomology. -/
def forgetCompactSupportCocone
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    Cocone (compactSupportDiagram X F n) where
  pt := ↧(CategoryTheory.Sheaf.H.{u, u} F n)
  ι :=
    { app K := AddCommGrpCat.ofHom (forgetClosedSupport X K.1 F n)
      naturality K L f := by
        ext α
        exact forgetClosedSupport_enlarge X (leOfHom f) F n α }

/-- The canonical map from compactly supported to ordinary sheaf cohomology. -/
def forgetCompactSupport
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    compactlySupportedCohomology X F n ⟶ ↧(CategoryTheory.Sheaf.H.{u, u} F n) :=
  colimit.desc _ (forgetCompactSupportCocone X F n)

@[reassoc (attr := simp)]
lemma toCompactlySupportedCohomology_forget (K : CompactCloseds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    toCompactlySupportedCohomology X K F n ≫ forgetCompactSupport X F n =
      AddCommGrpCat.ofHom (forgetClosedSupport X K.1 F n) :=
  colimit.ι_desc _ K

set_option maxHeartbeats 800000 in
/-- Forgetting compact support is natural in the coefficient sheaf. -/
def forgetCompactSupportNatTrans (n : ℕ) :
    compactlySupportedCohomologyFunctor X n ⟶
      CategoryTheory.Sheaf.functorH 𝓖[X] n where
  app F := forgetCompactSupport X F n
  naturality F G f := by
    apply colimit.hom_ext
    intro K
    change colimit.ι (compactSupportDiagram X F n) K ≫
        (colim.map
            ((CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip.map f) ≫
          forgetCompactSupport X G n) = _
    erw [colimit.ι_map_assoc]
    change ((cohomologyWithSupportFunctor X n).obj K.1).map f ≫
        (toCompactlySupportedCohomology X K G n ≫ forgetCompactSupport X G n) =
      toCompactlySupportedCohomology X K F n ≫
        (forgetCompactSupport X F n ≫
          (CategoryTheory.Sheaf.functorH 𝓖[X] n).map f)
    erw [toCompactlySupportedCohomology_forget,
      toCompactlySupportedCohomology_forget_assoc]
    exact forgetClosedSupport_naturality X K.1 f n

/-- On a compact space, compactly supported cohomology is ordinary sheaf cohomology. -/
def compactlySupportedCohomologyIso [CompactSpace X]
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    compactlySupportedCohomology X F n ≅ ↧(CategoryTheory.Sheaf.H.{u, u} F n) :=
  (colimit.isColimit (compactSupportDiagram X F n)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (CompactCloseds.isTerminalUniv X)
      (compactSupportDiagram X F n)) ≪≫ cohomologyWithSupportTopIso X F n

@[simp]
lemma compactlySupportedCohomologyIso_hom [CompactSpace X]
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (compactlySupportedCohomologyIso X F n).hom = forgetCompactSupport X F n := by
  apply colimit.hom_ext
  intro K
  dsimp only [compactlySupportedCohomologyIso, Iso.trans_hom]
  erw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
  rw [cohomologyWithSupportTopIso_hom]
  change _ = toCompactlySupportedCohomology X K F n ≫ forgetCompactSupport X F n
  rw [toCompactlySupportedCohomology_forget]
  ext α
  exact forgetClosedSupport_enlarge X (show K.1 ≤ ⊤ from le_top) F n α

end TopCat.Sheaf
