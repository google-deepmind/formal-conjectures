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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SupportedSingularSectionNaturality
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.CohomologySheafSection

/-!
# The supported singular cohomology sheaf and local relative cohomology

The restriction-natural local comparison is an isomorphism of presheaves, and exact
sheafification with its counit identifies the sheafification with the cohomology sheaf of
the kernel-defined supported singular complex. The local class and unit equations fix this
identification, including the positive short-exact-sequence lift normalization.
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

end AlgebraicTopology.Singular
