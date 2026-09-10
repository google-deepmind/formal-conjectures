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

public import FormalConjecturesForMathlib.AlgebraicTopology.OpenSheafification
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularSubdivisionCochainSheaf

/-! # Singular cochains and actual restriction to open subspaces -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u}) (U : Opens X)

/-- An open in an open subspace is identified with its actual ambient image. -/
def openSubspaceImageIso (V : Opens U) :
    (Opens.toTopCat (TopCat.of U)).obj V ≅
      (Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj V) :=
  TopCat.isoOfHomeo (U.isOpenEmbedding.toIsEmbedding.homeomorphImage (V : Set U))

@[reassoc]
lemma openSubspaceImageIso_naturality {V W : Opens U} (f : V ⟶ W) :
    (Opens.toTopCat (TopCat.of U)).map f ≫ (openSubspaceImageIso X U W).hom =
      (openSubspaceImageIso X U V).hom ≫
        (Opens.toTopCat X).map (U.isOpenEmbedding.functor.map f) :=
  TopCat.hom_ext rfl

/-- The actual ambient-image homeomorphisms induce chain isomorphisms. -/
def openSubspaceImageChainIso (V : Opens U) :
    (openSingularChainComplexFunctor R (TopCat.of U)).obj V ≅
      (openSingularChainComplexFunctor R X).obj (U.isOpenEmbedding.functor.obj V) :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapIso
    (openSubspaceImageIso X U V)

@[reassoc]
lemma openSubspaceImageChainIso_naturality {V W : Opens U} (f : V ⟶ W) :
    (openSingularChainComplexFunctor R (TopCat.of U)).map f ≫
      (openSubspaceImageChainIso R X U W).hom =
    (openSubspaceImageChainIso R X U V).hom ≫
      (openSingularChainComplexFunctor R X).map (U.isOpenEmbedding.functor.map f) := by
  dsimp only [openSubspaceImageChainIso, openSingularChainComplexFunctor,
    Functor.comp_map, Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp, openSubspaceImageIso_naturality]

/-- Restricting ambient raw singular cochains to the open subspace gives
intrinsic raw cochains there, by dualizing the actual image chain map. -/
def singularCochainPresheafOpenRestrictionIso (n : ℕ) :
    U.isOpenEmbedding.functor.op ⋙ singularCochainPresheaf R X n ≅
      singularCochainPresheaf R (TopCat.of U) n :=
  NatIso.ofComponents
    (fun V => (forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapIso
      ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℕ) n).mapIso
        (HomologicalComplex.linearDualIso (openSubspaceImageChainIso R X U V.unop))))
    (by
      intro V W f
      ext φ
      change OpenCochains R X (.op (U.isOpenEmbedding.functor.obj V.unop)) n at φ
      apply LinearMap.ext
      intro c
      exact congrArg φ (ConcreteCategory.congr_hom
        (congrArg (fun g => g.f n)
          (openSubspaceImageChainIso_naturality R X U f.unop)).symm c))

lemma singularCochainPresheafOpenRestrictionIso_coboundary (n : ℕ) :
    Functor.whiskerLeft U.isOpenEmbedding.functor.op (singularCochainCoboundary R X n) ≫
      (singularCochainPresheafOpenRestrictionIso R X U (n + 1)).hom =
    (singularCochainPresheafOpenRestrictionIso R X U n).hom ≫
      singularCochainCoboundary R (TopCat.of U) n := by
  apply NatTrans.ext
  funext V
  ext φ
  change OpenCochains R X (.op (U.isOpenEmbedding.functor.obj V.unop)) n at φ
  apply LinearMap.ext
  intro c
  exact congrArg φ (ConcreteCategory.congr_hom
    ((openSubspaceImageChainIso R X U V.unop).hom.comm (n + 1) n) c)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The raw open-subspace comparison respects the actual singular
coboundaries, and hence is an isomorphism of complexes. -/
def singularCochainPresheafComplexOpenRestrictionIso :
    (Functor.mapHomologicalComplex
      ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj U.isOpenEmbedding.functor.op)
      (.up ℕ)).obj (singularCochainPresheafComplex R X) ≅
    singularCochainPresheafComplex R (TopCat.of U) :=
  HomologicalComplex.Hom.isoOfComponents (singularCochainPresheafOpenRestrictionIso R X U)
    (by
      intro i j hij
      obtain rfl := hij
      rw [Functor.mapHomologicalComplex_obj_d, singularCochainPresheafComplex_d,
        singularCochainPresheafComplex_d]
      exact (singularCochainPresheafOpenRestrictionIso_coboundary R X U i).symm)

/-- Restriction of the ambient singular cochain sheaf is the intrinsic
singular cochain sheaf of the open subspace, with its unit normalization. -/
def singularCochainSheafOpenRestrictionIso (n : ℕ) :
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj (singularCochainSheaf R X n) ≅
      singularCochainSheaf R (TopCat.of U) n :=
  (TopCat.Sheaf.openRestrictionSheafificationIso X U (singularCochainPresheaf R X n)).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).mapIso
      (singularCochainPresheafOpenRestrictionIso R X U n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma singularCochainSheafOpenRestrictionIso_coboundary (n : ℕ) :
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
        (singularCochainSheafCoboundary R X n) ≫
      (singularCochainSheafOpenRestrictionIso R X U (n + 1)).hom =
    (singularCochainSheafOpenRestrictionIso R X U n).hom ≫
      singularCochainSheafCoboundary R (TopCat.of U) n := by
  apply (cancel_epi (TopCat.Sheaf.openRestrictionSheafificationIso X U
    (singularCochainPresheaf R X n)).hom).1
  dsimp only [singularCochainSheafOpenRestrictionIso, singularCochainSheafCoboundary]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← TopCat.Sheaf.openRestrictionSheafificationIso_naturality_assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp,
    singularCochainPresheafOpenRestrictionIso_coboundary]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual open restriction of the ambient sheafified singular
cochains is the intrinsic complex on that open subspace. -/
def singularCochainSheafComplexOpenRestrictionIso :
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
      (singularCochainSheafComplex R X) ≅
    singularCochainSheafComplex R (TopCat.of U) :=
  HomologicalComplex.Hom.isoOfComponents (singularCochainSheafOpenRestrictionIso R X U)
    (by
      intro i j hij
      obtain rfl := hij
      simpa only [Functor.mapHomologicalComplex_obj_d, singularCochainSheafComplex_d] using
        (singularCochainSheafOpenRestrictionIso_coboundary R X U i).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Unit normalization of the intrinsic/ambient singular sheaf comparison. -/
@[reassoc]
lemma toSheafify_singularCochainSheafOpenRestrictionIso (n : ℕ) :
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf R X n)) ≫
      (singularCochainSheafOpenRestrictionIso R X U n).hom.hom =
    (singularCochainPresheafOpenRestrictionIso R X U n).hom ≫
      toSheafify (Opens.grothendieckTopology (TopCat.of U))
        (singularCochainPresheaf R (TopCat.of U) n) := by
  rw [← TopCat.Sheaf.toSheafify_openRestrictionSheafificationIso]
  dsimp only [singularCochainSheafOpenRestrictionIso]
  rw [Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  simp only [Iso.symm_hom, Functor.mapIso_hom, ← Category.assoc,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.hom_inv_id]
  exact (toSheafify_naturality (Opens.grothendieckTopology (TopCat.of U))
    (singularCochainPresheafOpenRestrictionIso R X U n).hom).symm

end AlgebraicTopology.Singular
