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

public import FormalConjecturesForMathlib.AlgebraicTopology.HomologySheafSection
public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedSheafSupportLocalization
public import FormalConjecturesForMathlib.AlgebraicTopology.FlasqueQuasiIsoGlobalSections
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Cohomology-sheaf stalk vanishing from cofinal local section calculations

For a complex of additive sheaves, the stalk of the homology presheaf of its
underlying presheaf complex is canonically the stalk of its homology sheaf.
Both comparisons use exact stalk functors; evaluation on an open set is not
mistakenly treated as exact on sheaves.

Consequently, vanishing of section-complex homology on a cofinal system of
neighborhoods implies vanishing of the cohomology-sheaf stalk. The neighborhood
may depend on the original open set; no single neighborhood is silently
substituted for a cofinal family. This is the generic passage from the local
normal-slice calculation to sheaf support purity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- A presheaf whose sections vanish on cofinally small neighborhoods has zero stalk. -/
lemma isZero_stalk_of_cofinal_sections
    (P : Presheaf AddCommGrpCat.{u} X) (x : X)
    (hlocal : ∀ (U : Opens X), x ∈ U →
      ∃ (V : Opens X), V ≤ U ∧ x ∈ V ∧ IsZero (P.obj (op V))) :
    IsZero (P.stalk x) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  suffices h : ∀ a : P.stalk x, a = 0 from ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq a
  obtain ⟨V, hVU, hxV, hV⟩ := hlocal U hxU
  let := AddCommGrpCat.subsingleton_of_isZero hV
  have hs : P.map (homOfLE hVU).op s = 0 := Subsingleton.elim _ _
  rw [← P.germ_res_apply (homOfLE hVU) x hxV, hs, map_zero]

end TopCat.Presheaf

namespace TopCat.Sheaf

open AlgebraicTopology.Singular

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The presheaf homology of the actual underlying complex. This is not defined
as evaluation of the cohomology sheaf, since that evaluation is not exact. -/
def sectionCohomologyPresheaf (n : ℤ) : Presheaf AddCommGrpCat.{u} X :=
  (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).homology n

/-- Exact evaluation of presheaves identifies section-complex homology with
the homology presheaf on the same open set. -/
def sectionCohomologyPresheafOnOpenIso (n : ℤ) (U : Opens X) :
    (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅
      (sectionCohomologyPresheaf X K n).obj (op U) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    ((((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n)
  exact S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

/-- The homology presheaf and actual homology sheaf have canonically equal stalks.
The underlying sheaf-forgetful functor is not assumed exact. -/
def sectionCohomologyPresheafStalkIso (n : ℤ) (x : X) :
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (sectionCohomologyPresheaf X K n) ≅
      (additiveSheafStalkFunctor X x).obj (K.homology n) := by
  let S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    K.sc n
  let P : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n
  exact (P.mapHomologyIso (additivePresheafStalkFunctor X x)).symm ≪≫
    S.mapHomologyIso (additiveSheafStalkFunctor X x)

/-- Cohomology-sheaf stalk vanishing from actual section complexes on cofinally
small opens. This generic lemma exposes, rather than assumes, its local input. -/
lemma cohomologySheaf_stalk_isZero_of_cofinal_sections (n : ℤ) (x : X)
    (hlocal : ∀ (U : Opens X), x ∈ U →
      ∃ (V : Opens X), V ≤ U ∧ x ∈ V ∧
        IsZero ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj K).homology n)) :
    IsZero ((additiveSheafStalkFunctor X x).obj (K.homology n)) := by
  apply (sectionCohomologyPresheafStalkIso X K n x).isZero_iff.mp
  apply Presheaf.isZero_stalk_of_cofinal_sections
  intro U hxU
  obtain ⟨V, hVU, hxV, hV⟩ := hlocal U hxU
  exact ⟨V, hVU, hxV, (sectionCohomologyPresheafOnOpenIso X K n V).isZero_iff.mp hV⟩

/-- If all points admit the cofinal local calculation, the actual cohomology
sheaf vanishes globally. -/
lemma cohomologySheaf_isZero_of_cofinal_sections (n : ℤ)
    (hlocal : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), V ≤ U ∧ x ∈ V ∧
        IsZero ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj K).homology n)) :
    IsZero (K.homology n) := by
  exact (isZero_iff_stalkFunctor_obj_isZero _).mpr fun x =>
    cohomologySheaf_stalk_isZero_of_cofinal_sections X K n x (hlocal x)

/-- A map that is a quasi-isomorphism on sections on cofinally small opens is
a sheaf quasi-isomorphism. This uses the actual mapping cone, not exactness of
open-set evaluation on all sheaves. -/
lemma quasiIso_of_cofinal_section_quasiIso
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L)
    (hlocal : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ (V : Opens X), V ≤ U ∧ x ∈ V ∧
        QuasiIso (((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  apply IsFlasque.BoundedBelowComplex.quasiIso_of_mappingCone_acyclic
  intro n
  rw [exactAt_iff_isZero_homology]
  apply cohomologySheaf_isZero_of_cofinal_sections
  intro x U hxU
  obtain ⟨V, hVU, hxV, hV⟩ := hlocal x U hxU
  refine ⟨V, hVU, hxV, ?_⟩
  let F := supportEvaluation X V
  let : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := hV
  have h := IsFlasque.BoundedBelowComplex.mappingCone_acyclic_of_quasiIso
    ((F.mapHomologicalComplex (.up ℤ)).map f) n
  exact (homologyMapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F) n).isZero_iff.mpr
    h.isZero_homology

end TopCat.Sheaf
