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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.NestedSheafSupportLocalization
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.FlasqueSupportedSections
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SupportedSectionRestrictionCone
/-!
# The open-set model of the last localization term

For `V ≤ U`, global sections of the sheaf of sections on `U` vanishing on `V` are
canonically sections on `U` of the sheaf of ambient sections vanishing on `V`, both sides
being the kernel of restriction `F(U) → F(V)`. The comparison is functorial in the
coefficient sheaf, so it identifies the last complex in nested-support localization with
the supported-section complex on the complement of the smaller closed support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

theorem openRestrictionImage_top (U : Opens X) :
    openRestrictionImage X U ⊤ = U := by
  simpa only [top_inf_eq] using Opens.functor_map_eq_inf U (⊤ : Opens X)

theorem openRestrictionImage_eq_of_le {U V : Opens X} (h : V ≤ U) :
    openRestrictionImage X V U = V := by
  simpa only [inf_eq_right.mpr h] using Opens.functor_map_eq_inf V U

/-- The literal equality of opens identifies global sections of the open
pushforward with sections of the original sheaf on that open. -/
def openRestrictionPushforwardTopEvaluationIso (U : Opens X) :
    openRestrictionPushforward X U ⋙ supportEvaluation X ⊤ ≅ supportEvaluation X U :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (eqToIso (congrArg op (openRestrictionImage_top X U))))
    (fun f => (f.hom.naturality _).symm)

/-- The last localization kernel includes into the actual sections on `U`. -/
def sheafSectionsBetweenOpensInclusion {U V : Opens X} (h : V ≤ U) :
    sheafSectionsBetweenOpens X h ⟶ openRestrictionPushforward X U where
  app F := kernel.ι ((openRestrictionPushforwardMap X h).app F)
  naturality F G f := by simp [sheafSectionsBetweenOpens]

variable {U V : Opens X} (h : V ≤ U)

/-- The two target section groups are identified by their common actual open
`V`, using `V ≤ U`. -/
def nestedSupportRestrictionTargetIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((openRestrictionPushforward X V).obj F).obj.obj (op ⊤) ≅
      ((openRestrictionPushforward X V).obj F).obj.obj (op U) :=
  F.obj.mapIso (eqToIso (congrArg op
    ((openRestrictionImage_top X V).trans (openRestrictionImage_eq_of_le X h).symm)))

/-- The comparison of the two restriction arrows is the literal presheaf
restriction square, not a comparison supplied on cohomology. -/
@[reassoc]
theorem nestedSupportRestrictionTargetIso_square (F : Sheaf AddCommGrpCat.{u} X) :
    (((openRestrictionPushforwardMap X h).app F).hom.app (op ⊤)) ≫
        (nestedSupportRestrictionTargetIso X h F).hom =
      (openRestrictionPushforwardTopEvaluationIso X U).hom.app F ≫
        (((toOpenRestrictionPushforward X V).app F).hom.app (op U)) := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

/-- Canonical kernel comparison between the last global localization term and
supported sections on the actual open complement. -/
def sheafSectionsBetweenOpensGlobalIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsBetweenOpens X h).obj F).obj.obj (op ⊤) ≅
      ((sheafSectionsSupportedOutside X V).obj F).obj.obj (op U) :=
  sheafSectionsBetweenOpensOnOpenIso X h ⊤ F ≪≫
    kernel.mapIso _ _ ((openRestrictionPushforwardTopEvaluationIso X U).app F)
      (nestedSupportRestrictionTargetIso X h F)
      (nestedSupportRestrictionTargetIso_square X h F) ≪≫
    (sheafSectionsSupportedOutsideOnOpenIso X V U F).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison preserves the actual inclusion into sections on `U`. -/
@[reassoc (attr := simp)]
theorem sheafSectionsBetweenOpensGlobalIso_hom_inclusion
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) =
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
        (openRestrictionPushforwardTopEvaluationIso X U).hom.app F := by
  rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
  simp only [sheafSectionsBetweenOpensGlobalIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, kernel.mapIso_hom, kernel.map,
    kernel.lift_ι]
  rw [sheafSectionsBetweenOpensOnOpenIso_hom_ι_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality in the actual coefficient sheaf. -/
@[reassoc]
theorem sheafSectionsBetweenOpensGlobalIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (((sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
        (sheafSectionsBetweenOpensGlobalIso X h G).hom =
      (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        (((sheafSectionsSupportedOutside X V).map f).hom.app (op U)) := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U)) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U G]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have h₁ := congrArg (fun q => q.hom.app (op ⊤))
    ((sheafSectionsBetweenOpensInclusion X h).naturality f)
  have h₂ := congrArg (fun q => q.hom.app (op U))
    ((sheafSectionsSupportedOutsideInclusion X V).naturality f)
  change (((sheafSectionsSupportedOutside X V).map f).hom.app (op U)) ≫
      ((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U) =
    ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) ≫
      f.hom.app (op U) at h₂
  change (((sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app G).hom.app (op ⊤) =
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
      (((openRestrictionPushforward X U).map f).hom.app (op ⊤)) at h₁
  rw [Category.assoc, h₂, sheafSectionsBetweenOpensGlobalIso_hom_inclusion_assoc]
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (fun q =>
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫ q)
      ((openRestrictionPushforwardTopEvaluationIso X U).hom.naturality f)

/-- The comparison is a natural isomorphism of actual section functors. -/
def sheafSectionsBetweenOpensGlobalNatIso :
    sheafSectionsBetweenOpens X h ⋙ supportEvaluation X ⊤ ≅
      sheafSectionsSupportedOutside X V ⋙ supportEvaluation X U :=
  NatIso.ofComponents (sheafSectionsBetweenOpensGlobalIso X h)
    (fun f => sheafSectionsBetweenOpensGlobalIso_naturality X h f)

/-- The last complex in global nested-support localization is the actual
supported-section complex on the complement `U` of the smaller support. -/
def nestedSupportRestrictionLastComplexIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).X₃ ≅
      ((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj
        (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K) :=
  (NatIso.mapHomologicalComplex (sheafSectionsBetweenOpensGlobalNatIso X h) (.up ℤ)).app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The last localization map, under the proved kernel comparison, is
literally restriction of the supported section to `U`. -/
@[reassoc]
theorem toSheafSectionsBetweenOpens_global_comparison
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
        (sheafSectionsBetweenOpensGlobalIso X h F).hom =
      ((sheafSectionsSupportedOutside X V).obj F).obj.map (homOfLE (le_top : U ≤ ⊤)).op := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U)) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have hι := ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  rw [hι, ← Category.assoc]
  have hg : ((toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) =
    ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op ⊤) ≫
      ((toOpenRestrictionPushforward X U).app F).hom.app (op ⊤) := by
    change (((toSheafSectionsBetweenOpens X h).app F) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F)).hom.app (op ⊤) = _
    simp only [toSheafSectionsBetweenOpens, sheafSectionsBetweenOpensInclusion,
      kernel.map, kernel.lift_ι]
    rfl
  rw [hg, Category.assoc]
  congr 1
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The last-complex identification retains the literal restriction map,
before passage to homology. -/
@[reassoc]
theorem nestedSupportRestrictionLastComplexIso_g
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).g ≫
        (nestedSupportRestrictionLastComplexIso X h K).hom =
      sectionComplexRestriction X (.up ℤ)
        (((sheafSectionsSupportedOutside X V).mapHomologicalComplex (.up ℤ)).obj K)
        (homOfLE (le_top : U ≤ ⊤)) := by
  ext n : 1
  exact toSheafSectionsBetweenOpens_global_comparison X h (K.X n)

end TopCat.Sheaf
