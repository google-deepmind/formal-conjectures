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

public import FormalConjecturesForMathlib.AlgebraicTopology.FlasqueSupportedSections
public import FormalConjecturesForMathlib.AlgebraicTopology.FlasqueSheafSupportComparison
public import FormalConjecturesForMathlib.Algebra.Homology.MapExtend

/-!
# Actual supported-section kernels and open restriction cones

For a termwise flasque coefficient complex, the literal kernel-defined supported section
complex computes the cone of restriction from `V` to `V ∩ U`, with the conventional degree
shift. The arrow identification displays the actual open-intersection map. No arbitrary
local comparison, acyclicity, or purity equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Restriction between the actual open-section evaluation functors. -/
def supportEvaluationRestriction {V W : Opens X} (i : W ⟶ V) :
    supportEvaluation X V ⟶ supportEvaluation X W where
  app F := F.obj.map i.op
  naturality _F _G f := (f.hom.naturality i.op).symm

/-- The actual restriction morphism of section complexes, in any grading. -/
def sectionComplexRestriction {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {V W : Opens X} (i : W ⟶ V) :
    ((supportEvaluation X V).mapHomologicalComplex c).obj K ⟶
      ((supportEvaluation X W).mapHomologicalComplex c).obj K :=
  ((supportEvaluationRestriction X i).mapHomologicalComplex c).app K

/-- Actual section restriction commutes with extension from natural to integer degrees. -/
theorem sectionComplexRestriction_extend
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    sectionComplexRestriction X (.up ℤ) (K.extend ComplexShape.embeddingUpNat) i ≫
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) K
        ComplexShape.embeddingUpNat).hom =
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) K
        ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.mapExtendCanonicalIso_natTrans (supportEvaluation X V) K
    ComplexShape.embeddingUpNat (supportEvaluationRestriction X i)

/-- The corresponding actual restriction cones agree under the canonical grading comparison. -/
def sectionComplexRestrictionExtendConeIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    CochainComplex.mappingCone
      (sectionComplexRestriction X (.up ℤ) (K.extend ComplexShape.embeddingUpNat) i) ≅
      CochainComplex.mappingCone
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) K i)
          ComplexShape.embeddingUpNat) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) K
        ComplexShape.embeddingUpNat)
      (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) K
        ComplexShape.embeddingUpNat)
      (sectionComplexRestriction_extend X K i).symm)

variable (U V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The third term of the actual support sequence is sections on the actual intersection. -/
def supportRestrictionSectionsIntersectionIso :
    (supportRestrictionSectionsComplexShortComplex X U V K).X₃ ≅
      ((supportEvaluation X (V ⊓ U)).mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => supportedOutsideIntersectionIso X U V (K.X n))
    (fun n m _ => (K.d n m).hom.naturality
      (eqToHom (congrArg op (Opens.functor_map_eq_inf U V))))

/-- The intersection identification preserves the literal restriction arrow. -/
theorem supportRestrictionSectionsIntersectionIso_restriction :
    (supportRestrictionSectionsComplexShortComplex X U V K).g ≫
      (supportRestrictionSectionsIntersectionIso X U V K).hom =
        sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U) :=
  HomologicalComplex.Hom.ext (funext fun n ↦
    toOpenRestrictionPushforward_intersection X U V (K.X n))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The cone of the actual support-sequence arrow is the cone of actual open restriction. -/
def supportRestrictionSectionsConeIso :
    CochainComplex.mappingCone (supportRestrictionSectionsComplexShortComplex X U V K).g ≅
      CochainComplex.mappingCone
        (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U)) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by omega)⟩)
    (Arrow.isoMk (Iso.refl _) (supportRestrictionSectionsIntersectionIso X U V K)
      (by simpa using (supportRestrictionSectionsIntersectionIso_restriction X U V K).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A flasque supported-section kernel computes the true restriction cone, with
supported degree `n` corresponding to cone degree `n - 1`. -/
def supportedSectionHomologyIsoRestrictionCone
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    (supportRestrictionSectionsComplexShortComplex X U V K).X₁.homology n ≅
      (CochainComplex.mappingCone
        (sectionComplexRestriction X (.up ℤ) K (Opens.infLELeft V U))).homology (n - 1) := by
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  let : QuasiIso (CochainComplex.mappingCocone.shiftedLiftShortComplex S) :=
    CochainComplex.mappingCocone.quasiIso_shiftedLiftShortComplex S
      (supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK)
  let e := ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) 0).shiftIso
    1 (n - 1) n (by omega)).app S.X₁
  exact e.symm ≪≫
    asIso (HomologicalComplex.homologyMap
      (CochainComplex.mappingCocone.shiftedLiftShortComplex S) (n - 1)) ≪≫
    HomologicalComplex.homologyMapIso (supportRestrictionSectionsConeIso X U V K) (n - 1)

/-- On an open contained in the excluded open, the actual supported-section group is
zero because its defining restriction map is an isomorphism. -/
theorem supportedOutsideSections_isZero_of_le (F : Sheaf AddCommGrpCat.{u} X)
    (hVU : V ≤ U) :
    IsZero (((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V)) := by
  have he : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hVU]
  have hi : IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V) := by
    rw [show U.isOpenEmbedding.isOpenMap.adjunction.counit.app V = eqToHom he from
      Subsingleton.elim _ _]
    infer_instance
  let r := ((toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have : IsIso r := by
    change IsIso (F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op)
    infer_instance
  exact (isZero_kernel_of_mono r).of_iso (sheafSectionsSupportedOutsideOnOpenIso X U V F)

end TopCat.Sheaf
