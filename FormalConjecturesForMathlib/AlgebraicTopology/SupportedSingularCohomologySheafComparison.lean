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

public import FormalConjecturesForMathlib.AlgebraicTopology.SupportedSingularSectionNaturality
public import FormalConjecturesForMathlib.AlgebraicTopology.CohomologySheafSection

/-!
# The actual supported singular cohomology sheaf and local relative cohomology

The previously constructed, restriction-natural local comparison is an
isomorphism of presheaves. Exact sheafification and its actual counit then
identify its sheafification with the cohomology sheaf of the kernel-defined
supported singular complex. The local class and unit equations fix this
identification, including the positive short-exact-sequence lift normalization.

No assertion that open evaluation is exact on sheaves is used. Nor is a
presheaf gluing or local-purity theorem assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The canonical evaluation/homology comparison respects actual open restriction. -/
@[reassoc]
lemma sectionCohomologyPresheafOnOpenIso_inv_naturality
    (n : ℤ) {V W : Opens X} (a : W ⟶ V) :
    (sectionCohomologyPresheaf X K n).map a.op ≫
      (sectionCohomologyPresheafOnOpenIso X K n W).inv =
    (sectionCohomologyPresheafOnOpenIso X K n V).inv ≫
      homologyMap (sectionComplexRestriction X (.up ℤ) K a) n := by
  let P : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := P.sc n
  change ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op).app S.homology ≫
      (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op W))).inv =
    (S.mapHomologyIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))).inv ≫
      ShortComplex.homologyMap
        (S.mapNatTrans ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).map a.op))
  rw [NatTrans.app_homology]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end TopCat.Sheaf

namespace AlgebraicTopology.Singular

open TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (S : Set X) (hS : IsClosed S) (n : ℕ)

/-- The actual local cohomology presheaf of supported singular cochains is the
literal relative-cohomology presheaf, with its literal pair restrictions. -/
def supportedSingularCohomologyPresheafIsoRelative :
    sectionCohomologyPresheaf X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) ≅
        supportRelativeCohomologyPresheaf X S n :=
  NatIso.ofComponents (fun V =>
    (sectionCohomologyPresheafOnOpenIso X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V.unop).symm ≪≫
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V.unop n).toAddCommGrpIso) (by
    intro V W a
    apply ConcreteCategory.hom_ext
    intro z
    let K := supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩
    change supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS W.unop n
        ((sectionCohomologyPresheafOnOpenIso X K (n : ℤ) W.unop).inv
          ((sectionCohomologyPresheaf X K (n : ℤ)).map a z)) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap
          (W := (W.unop : Set X)) (V := (V.unop : Set X)) (leOfHom a.unop) S)
        (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V.unop n
          ((sectionCohomologyPresheafOnOpenIso X K (n : ℤ) V.unop).inv z))
    have h := ConcreteCategory.congr_hom
      (sectionCohomologyPresheafOnOpenIso_inv_naturality X K (n : ℤ) a.unop) z
    simp only [ConcreteCategory.comp_apply, Quiver.Hom.op_unop] at h
    rw [h]
    exact supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
      X S hS a.unop n _)

/-- Exact sheafification identifies the actual supported cohomology sheaf with
the sheafification of literal neighborhood/support relative cohomology. -/
def supportedSingularCohomologySheafIsoRelative :
    (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩).homology (n : ℤ) ≅
      supportRelativeCohomologySheaf X S n :=
  (sectionCohomologyPresheafSheafificationIso X
    (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ)).symm ≪≫
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (supportedSingularCohomologyPresheafIsoRelative X S hS n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sheaf comparison preserves the actual sheafification unit. -/
@[reassoc]
lemma supportedSingularCohomologySheafIsoRelative_unit :
    sectionCohomologyPresheafToSheaf X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) ≫
        (supportedSingularCohomologySheafIsoRelative X S hS n).hom.hom =
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom ≫
      supportRelativeCohomologyToSheaf X S n := by
  dsimp only [sectionCohomologyPresheafToSheaf, supportedSingularCohomologySheafIsoRelative,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, supportRelativeCohomologyToSheaf]
  let e := sectionCohomologyPresheafSheafificationIso X
    (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ)
  let m := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom
  have he : e.hom.hom ≫ (e.inv ≫ m).hom = m.hom :=
    congrArg (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (Iso.hom_inv_id_assoc e m)
  rw [Category.assoc, he]
  exact (toSheafify_naturality (Opens.grothendieckTopology X)
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom).symm

/-- An actual local section-complex class maps to its actual relative class
followed by the relative sheafification unit. This fixes the local normalization. -/
@[reassoc]
lemma supportedSingularCohomologySheafIsoRelative_section (V : Opens X) :
    sectionCohomologyToSheafSection X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V ≫
        (supportedSingularCohomologySheafIsoRelative X S hS n).hom.hom.app (op V) =
    (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf X S n).app (op V) := by
  dsimp only [sectionCohomologyToSheafSection]
  rw [Category.assoc, ← NatTrans.comp_app, supportedSingularCohomologySheafIsoRelative_unit,
    NatTrans.comp_app, ← Category.assoc]
  dsimp only [supportedSingularCohomologyPresheafIsoRelative, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]

/-- Inverse transport of a represented relative section recovers the canonical
section of the actual cohomology sheaf, without changing its normalization. -/
lemma supportedSingularCohomologySheafIsoRelative_inv_section (V : Opens X)
    (z : ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    (supportedSingularCohomologySheafIsoRelative X S hS n).inv.hom.app (op V)
      ((supportRelativeCohomologyToSheaf X S n).app (op V)
        (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z)) =
    sectionCohomologyToSheafSection X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V z := by
  have h := ConcreteCategory.congr_hom
    (supportedSingularCohomologySheafIsoRelative_section X S hS n V) z
  simp only [ConcreteCategory.comp_apply] at h
  exact (congrArg ((supportedSingularCohomologySheafIsoRelative X S hS n).inv.hom.app (op V))
    h.symm).trans (ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V))
        (supportedSingularCohomologySheafIsoRelative X S hS n).hom_inv_id) _)

/-- Exact stalk normalization: the actual local class germ maps to the germ
of its literal relative coclass under the sheaf comparison. -/
lemma supportedSingularCohomologySheafIsoRelative_germ
    (V : Opens X) (x : X) (hx : x ∈ V)
    (z : ((((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩))).homology (n : ℤ)) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (supportedSingularCohomologySheafIsoRelative X S hS n).hom.hom
      (((supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩).homology
        (n : ℤ)).presheaf.germ V x hx
        (sectionCohomologyToSheafSection X
          (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V z)) =
    supportRelativeCohomologyGerm X S n V x hx
      (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n z) := by
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  apply congrArg ((supportRelativeCohomologySheaf X S n).presheaf.germ V x hx)
  exact ConcreteCategory.congr_hom
    (supportedSingularCohomologySheafIsoRelative_section X S hS n V) z

end AlgebraicTopology.Singular
