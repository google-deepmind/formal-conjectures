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
public import FormalConjecturesForMathlib.CategoryTheory.Abelian.KernelCompositionShortExact
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Localization between two nested closed supports

For `V ⊆ U` open, the actual restrictions `F → j_{U*}F|U → j_{V*}F|V`
give a short exact sequence on injective coefficients:
`0 → Γ̲_{X∖U} F → Γ̲_{X∖V} F → ker(j_{U*}F|U → j_{V*}F|V) → 0`.
The last term is explicitly the sheaf of sections on `U` vanishing on `V`,
viewed on `X`. Thus for closed supports `S ⊆ Z`, the sequence removes `S`
from `Z`, by taking `U = X∖S` and `V = X∖Z`.

Exactness persists on every open set, since the first restriction is onto for
injective (indeed flasque) coefficients. No local purity or dimension vanishing
is assumed here. The resulting canonical mapping-fiber comparison is the
algebraic localization step needed when extending over singular strata.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) {U V : Opens X} (h : V ≤ U)

/-- Sections on `U` vanishing on `V`, pushed to the original ambient space. -/
def sheafSectionsBetweenOpens : Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := kernel ((openRestrictionPushforwardMap X h).app F)
  map f := kernel.map _ _ ((openRestrictionPushforward X U).map f)
    ((openRestrictionPushforward X V).map f)
    ((openRestrictionPushforwardMap X h).naturality f).symm
  map_id F := by
    apply (cancel_mono (kernel.ι _)).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance : (sheafSectionsBetweenOpens X h).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp [sheafSectionsBetweenOpens, Preadditive.add_comp, Preadditive.comp_add]

/-- On each ambient open set the last term is exactly the kernel of actual
restriction from its intersection with `U` to its intersection with `V`. -/
def sheafSectionsBetweenOpensOnOpenIso (W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsBetweenOpens X h).obj F).obj.obj (op W) ≅
      kernel (((openRestrictionPushforwardMap X h).app F).hom.app (op W)) :=
  PreservesKernel.iso (supportEvaluation X W) ((openRestrictionPushforwardMap X h).app F)

@[reassoc (attr := simp)]
lemma sheafSectionsBetweenOpensOnOpenIso_hom_ι (W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsBetweenOpensOnOpenIso X h W F).hom ≫
        kernel.ι (((openRestrictionPushforwardMap X h).app F).hom.app (op W)) =
      (kernel.ι ((openRestrictionPushforwardMap X h).app F)).hom.app (op W) :=
  kernelComparison_comp_ι ((openRestrictionPushforwardMap X h).app F) (supportEvaluation X W)

/-- Restrict an ambient section vanishing on `V` to its section on `U`. -/
def toSheafSectionsBetweenOpens :
    sheafSectionsSupportedOutside X V ⟶ sheafSectionsBetweenOpens X h where
  app F := kernel.map ((toOpenRestrictionPushforward X V).app F)
    ((openRestrictionPushforwardMap X h).app F)
    ((toOpenRestrictionPushforward X U).app F) (𝟙 _)
    (by simpa only [Category.comp_id, NatTrans.comp_app] using
      (NatTrans.congr_app (toOpenRestrictionPushforward_comp X h) F).symm)
  naturality F G f := by
    apply (cancel_mono (kernel.ι ((openRestrictionPushforwardMap X h).app G))).1
    simp only [sheafSectionsSupportedOutside, sheafSectionsBetweenOpens, kernel.map,
      kernel.lift_ι, Category.assoc, kernel.lift_ι_assoc]
    exact congrArg
      (fun q => kernel.ι ((toOpenRestrictionPushforward X V).app F) ≫ q)
      ((toOpenRestrictionPushforward X U).naturality f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting a section supported outside `U` to `U` gives zero. -/
@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideMap_toBetween :
    sheafSectionsSupportedOutsideMap X h ≫ toSheafSectionsBetweenOpens X h = 0 := by
  apply NatTrans.ext
  funext F
  apply (cancel_mono (kernel.ι _)).1
  simp [toSheafSectionsBetweenOpens, sheafSectionsSupportedOutsideMap,
    liftSheafSectionsSupportedOutside, sheafSectionsSupportedOutsideInclusion]

/-- The actual inclusion/restriction sequence for two nested complements. -/
def nestedSupportRestrictionShortComplex (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((sheafSectionsSupportedOutsideMap X h).app F)
    ((toSheafSectionsBetweenOpens X h).app F)
    (NatTrans.congr_app (sheafSectionsSupportedOutsideMap_toBetween X h) F)

/-- The support sequence is precisely the canonical sequence of three kernels. -/
lemma nestedSupportRestrictionShortComplex_eq (F : Sheaf AddCommGrpCat.{u} X) :
    nestedSupportRestrictionShortComplex X h F =
      kernelFactorizationShortComplex
        ((toOpenRestrictionPushforward X U).app F)
        ((openRestrictionPushforwardMap X h).app F)
        ((toOpenRestrictionPushforward X V).app F)
        (NatTrans.congr_app (toOpenRestrictionPushforward_comp X h) F) := by
  simp [nestedSupportRestrictionShortComplex, kernelFactorizationShortComplex,
    sheafSectionsSupportedOutsideMap, liftSheafSectionsSupportedOutside,
    toSheafSectionsBetweenOpens, kernel.map, sheafSectionsSupportedOutside,
    sheafSectionsBetweenOpens, sheafSectionsSupportedOutsideInclusion]

/-- Injective coefficients give the actual short exact nested-support sequence. -/
lemma nestedSupportRestrictionShortComplex_shortExact
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    (nestedSupportRestrictionShortComplex X h F).ShortExact := by
  rw [nestedSupportRestrictionShortComplex_eq]
  exact kernelFactorizationShortComplex_shortExact _ _ _ _

/-- Exactness after evaluation is proved using flasqueness, not by treating
global sections as an exact functor. -/
lemma nestedSupportRestrictionSectionsShortComplex_shortExact (W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    ((nestedSupportRestrictionShortComplex X h F).map (supportEvaluation X W)).ShortExact := by
  rw [nestedSupportRestrictionShortComplex_eq]
  have : Epi ((supportEvaluation X W).map ((toOpenRestrictionPushforward X U).app F)) :=
    toOpenRestrictionPushforward_app_epi X U F W
  exact kernelFactorizationShortComplex_map_shortExact _ _ _ _ _

/-- The coefficientwise nested-support sequence on a complex of sheaves. -/
def nestedSupportRestrictionComplexShortComplex
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :=
  ShortComplex.mk
    (((sheafSectionsSupportedOutsideMap X h).mapHomologicalComplex (.up ℤ)).app K)
    (((toSheafSectionsBetweenOpens X h).mapHomologicalComplex (.up ℤ)).app K)
    (by ext n; exact NatTrans.congr_app (sheafSectionsSupportedOutsideMap_toBetween X h) (K.X n))

lemma nestedSupportRestrictionComplexShortComplex_shortExact
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (nestedSupportRestrictionComplexShortComplex X h K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => nestedSupportRestrictionShortComplex_shortExact X h (K.X n)

/-- The actual nested-support sequence of section complexes on an open set. -/
def nestedSupportRestrictionSectionsComplexShortComplex (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ) :=
  (nestedSupportRestrictionComplexShortComplex X h K).map
    ((supportEvaluation X W).mapHomologicalComplex (.up ℤ))

lemma nestedSupportRestrictionSectionsComplexShortComplex_shortExact (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => nestedSupportRestrictionSectionsShortComplex_shortExact X h W (K.X n)

/-- The canonical comparison from sections with the smaller closed support to
the homotopy fiber of restriction away from it inside the larger support. -/
def nestedSupportRestrictionToFiber (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁ ⟶
      CochainComplex.mappingCocone
        (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g :=
  CochainComplex.mappingCocone.liftShortComplex _

lemma nestedSupportRestrictionToFiber_quasiIso (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)] :
    QuasiIso (nestedSupportRestrictionToFiber X h W K) :=
  CochainComplex.mappingCocone.quasiIso_liftShortComplex _
    (nestedSupportRestrictionSectionsComplexShortComplex_shortExact X h W K)

/-- The fiber comparison preserves the literal support-enlargement map. -/
@[reassoc (attr := simp)]
lemma nestedSupportRestrictionToFiber_fst (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    nestedSupportRestrictionToFiber X h W K ≫ CochainComplex.mappingCocone.fst _ =
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).f :=
  CochainComplex.mappingCocone.liftShortComplex_fst _

/-- Removing the smaller support preserves degree `n` cohomology if its two
adjacent groups vanish. These are explicit hypotheses of the extension lemma;
no vanishing statement about a singular locus is asserted here. -/
lemma nestedSupportRestriction_homologyMap_isIso_of_vanishing (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    IsIso (HomologicalComplex.homologyMap
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n) := by
  let S := nestedSupportRestrictionSectionsComplexShortComplex X h W K
  have hS := nestedSupportRestrictionSectionsComplexShortComplex_shortExact X h W K
  have : Mono (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₂ n).mono_g (hn.eq_zero_of_src _)
  have : Epi (HomologicalComplex.homologyMap S.g n) :=
    (hS.homology_exact₃ n (n + 1) (by simp)).epi_f (hn₁.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The extension equivalence is the inverse of actual restriction, rather
than an arbitrarily chosen linear equivalence between cohomology groups. -/
def nestedSupportRestrictionHomologyIsoOfVanishing (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₂.homology n ≅
      (nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₃.homology n := by
  have := nestedSupportRestriction_homologyMap_isIso_of_vanishing X h W K n hn hn₁
  exact asIso (HomologicalComplex.homologyMap
    (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n)

@[simp]
lemma nestedSupportRestrictionHomologyIsoOfVanishing_hom (W : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) [∀ n, Injective (K.X n)]
    (n : ℤ)
    (hn : IsZero ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology n))
    (hn₁ : IsZero
      ((nestedSupportRestrictionSectionsComplexShortComplex X h W K).X₁.homology (n + 1))) :
    (nestedSupportRestrictionHomologyIsoOfVanishing X h W K n hn hn₁).hom =
      HomologicalComplex.homologyMap
        (nestedSupportRestrictionSectionsComplexShortComplex X h W K).g n := rfl

end TopCat.Sheaf
