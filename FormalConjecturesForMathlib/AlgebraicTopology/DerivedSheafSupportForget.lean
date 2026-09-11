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

public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupportNaturality
public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupportLocalization

/-!
# Forgetting closed support in actual derived sections

The support-forgetting morphism is derived from the actual kernel inclusion into
global sections. With whole-space support this is canonically an isomorphism.
The factorization through support enlargement and all shift compatibilities are
proved, so the comparison introduces no independent normalization datum.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- The actual inclusion of globally supported sections into all global sections. -/
def closedSupportSectionsInclusion (Z : Closeds X) :
    closedSupportSections X Z ⟶ supportEvaluation X ⊤ :=
  Functor.whiskerRight (sheafSectionsSupportedOutsideInclusion X Z.compl)
    (supportEvaluation X ⊤) ≫ (supportEvaluation X ⊤).leftUnitor.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Enlarging support does not change the underlying global section. -/
@[reassoc (attr := simp)]
theorem closedSupportSectionsMap_inclusion {Z W : Closeds X} (h : Z ≤ W) :
    closedSupportSectionsMap X h ≫ closedSupportSectionsInclusion X W =
      closedSupportSectionsInclusion X Z := by
  ext F : 2
  change (supportEvaluation X ⊤).map _ ≫
      ((supportEvaluation X ⊤).map _ ≫ 𝟙 _) =
    (supportEvaluation X ⊤).map _ ≫ 𝟙 _
  simp only [Category.comp_id, ← Functor.map_comp]
  congr 1
  exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_inclusion X
    (show W.compl ≤ Z.compl from fun _ hx hz ↦ hx (h hz))) F

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In whole-space support the inclusion is the canonical kernel-of-zero isomorphism. -/
instance closedSupportSectionsInclusion_top_isIso :
    IsIso (closedSupportSectionsInclusion X ⊤) := by
  have h : (⊤ : Closeds X).compl = ⊥ := by ext; simp
  have : IsIso (sheafSectionsSupportedOutsideInclusion X (⊤ : Closeds X).compl) := by
    rw [h]
    exact NatIso.isIso_of_isIso_app _
  unfold closedSupportSectionsInclusion
  infer_instance

/-- Whole-space supported sections are all global sections, through their actual inclusion. -/
def closedSupportSectionsTopIso : closedSupportSections X ⊤ ≅ supportEvaluation X ⊤ :=
  asIso (closedSupportSectionsInclusion X ⊤)

local instance derivedSupportForgetSheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance derivedSupportForgetGroupDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

/-- Actual derived global sections, obtained by right deriving global evaluation. -/
def derivedGlobalSections :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  (supportEvaluation X ⊤).rightDerivedFunctorPlus

instance derivedGlobalSections_commShift : (derivedGlobalSections X).CommShift ℤ :=
  inferInstanceAs ((supportEvaluation X ⊤).rightDerivedFunctorPlus.CommShift ℤ)

/-- Forget closed support by deriving the actual inclusion of sections. -/
def derivedForgetClosedSupport (Z : Closeds X) :
    derivedClosedSupportSections X Z ⟶ derivedGlobalSections X :=
  (closedSupportSectionsInclusion X Z).rightDerivedFunctorPlus

instance derivedForgetClosedSupport_commShift (Z : Closeds X) :
    NatTrans.CommShift (derivedForgetClosedSupport X Z) ℤ :=
  inferInstanceAs
    (NatTrans.CommShift (closedSupportSectionsInclusion X Z).rightDerivedFunctorPlus ℤ)

/-- Derived whole-space support is canonically the actual derived global-sections functor. -/
def derivedClosedSupportSectionsTopIso :
    derivedClosedSupportSections X ⊤ ≅ derivedGlobalSections X :=
  NatIso.rightDerivedFunctorPlus (closedSupportSectionsTopIso X)

/-- The whole-space isomorphism is exactly support forgetting, not a separately chosen map. -/
@[simp]
theorem derivedClosedSupportSectionsTopIso_hom :
    (derivedClosedSupportSectionsTopIso X).hom = derivedForgetClosedSupport X ⊤ := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Actual support forgetting factors through enlargement to the whole space. -/
@[reassoc (attr := simp)]
theorem derivedClosedSupportSectionsMap_forget {Z W : Closeds X} (h : Z ≤ W) :
    derivedClosedSupportSectionsMap X h ≫ derivedForgetClosedSupport X W =
      derivedForgetClosedSupport X Z := by
  unfold derivedClosedSupportSectionsMap derivedForgetClosedSupport
  rw [← NatTrans.rightDerivedFunctorPlus_comp, closedSupportSectionsMap_inclusion]

/-- The derived-unit square pins support forgetting to its sectionwise kernel inclusion. -/
@[reassoc (attr := simp)]
theorem derivedForgetClosedSupport_unit_app (Z : Closeds X)
    (K : HomotopyCategory.Plus (Sheaf AddCommGrpCat.{u} X)) :
    (derivedClosedSupportSectionsUnit X Z).app K ≫
        (derivedForgetClosedSupport X Z).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((closedSupportSectionsInclusion X Z).mapHomotopyCategoryPlus.app K) ≫
        (supportEvaluation X ⊤).rightDerivedFunctorPlusUnit.app K :=
  (closedSupportSectionsInclusion X Z).rightDerivedFunctorPlus_unit_app K

end TopCat.Sheaf
