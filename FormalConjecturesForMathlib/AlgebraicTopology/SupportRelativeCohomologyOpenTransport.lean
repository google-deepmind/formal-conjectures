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

public import FormalConjecturesForMathlib.AlgebraicTopology.SupportRelativeCohomologySheaf
public import FormalConjecturesForMathlib.AlgebraicTopology.NeighborhoodSupportPairImage
public import FormalConjecturesForMathlib.AlgebraicTopology.OpenSheafification

/-!
# Actual open-embedding transport of the relative-cohomology sheaf

Neighborhood/support pairs are identified with their images by the actual
embedding homeomorphisms. These identifications commute with literal pair
inclusions and hence give a presheaf isomorphism. Actual sheafification then
transports the normalized section, with the sheafification-unit square displayed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- The pair-image identification respects literal neighborhood inclusions. -/
theorem neighborhoodSupportPairImageIso_naturality {U V : Opens Y} (hUV : U ≤ V) :
    neighborhoodSupportInclusionPairMap (W := (U : Set Y)) (V := (V : Set Y)) hUV B ≫
      (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
        (fun y _ => by rw [← hB]; rfl)).hom =
    (neighborhoodSupportPairImageIso f hf.isEmbedding (U : Set Y) B S
      (fun y _ => by rw [← hB]; rfl)).hom ≫
      neighborhoodSupportInclusionPairMap
        (W := (hf.functor.obj U : Set X)) (V := (hf.functor.obj V : Set X))
        (Set.image_mono hUV) S := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Literal pair pullback is the forward component of the constructed equivalence. -/
theorem neighborhoodSupportPairImageCohomologyEquiv_apply (V : Opens Y) (n : ℕ)
    (a : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (hf.functor.obj V : Set X) S) n) :
    neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding (V : Set Y) B S
      (fun y _ => by rw [← hB]; rfl) n a =
    relativeCohomologyMap ℚ n
      (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
        (fun y _ => by rw [← hB]; rfl)).hom a := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The presheaf comparison comes from the actual pair-image homeomorphisms. -/
def supportRelativeCohomologyPresheafOpenIso (n : ℕ) :
    hf.functor.op ⋙ supportRelativeCohomologyPresheaf X S n ≅
      supportRelativeCohomologyPresheaf Y B n :=
  NatIso.ofComponents (fun V =>
    (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding (V.unop : Set Y) B S
      (fun y _ => by rw [← hB]; rfl) n).toAddEquiv.toAddCommGrpIso) (by
    intro U V g
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V.unop : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).hom
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportInclusionPairMap (Set.image_mono (leOfHom g.unop)) S) a) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (V.unop : Set Y))
          (V := (U.unop : Set Y)) (leOfHom g.unop) B)
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportPairImageIso f hf.isEmbedding (U.unop : Set Y) B S
            (fun y _ => by rw [← hB]; rfl)).hom a)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      ← neighborhoodSupportPairImageIso_naturality f hf S B hB (leOfHom g.unop),
      relativeCohomologyMap_comp]
    rfl)

/-- Inverse transport is literal pullback along the inverse pair homeomorphism. -/
theorem supportRelativeCohomologyPresheafOpenIso_inv_app (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op V) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).inv a := rfl

/-- The open-image functor commutes with sheafification, through the actual
restricted unit. This is the general open-embedding version of open restriction. -/
def supportOpenEmbeddingSheafificationIso (P : TopCat.Presheaf AddCommGrpCat X) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj (hf.functor.op ⋙ P) ≅
      (hf.sheafPullback AddCommGrpCat).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isContinuous
  let : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isCocontinuous
  exact (hf.functor.pushforwardContinuousSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).app P

@[reassoc]
theorem supportOpenEmbeddingSheafificationIso_unit (P : TopCat.Presheaf AddCommGrpCat X) :
    toSheafify (Opens.grothendieckTopology Y) (hf.functor.op ⋙ P) ≫
      (supportOpenEmbeddingSheafificationIso f hf P).hom.hom =
    Functor.whiskerLeft hf.functor.op (toSheafify (Opens.grothendieckTopology X) P) := by
  let : hf.functor.IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isContinuous
  let : hf.functor.IsCocontinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    hf.functor_isCocontinuous
  exact hf.functor.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) P

/-- Actual sheafification of the pair comparison identifies intrinsic local support
cohomology with restriction of the original ambient relative-cohomology sheaf. -/
def supportRelativeCohomologySheafOpenIso (n : ℕ) :
    supportRelativeCohomologySheaf Y B n ≅
      (hf.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf X S n) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapIso
      (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).symm ≪≫
    supportOpenEmbeddingSheafificationIso f hf (supportRelativeCohomologyPresheaf X S n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalization square: actual classes are transported through their literal
pair-homeomorphism pullbacks before application of the ambient sheafification unit. -/
@[reassoc]
theorem supportRelativeCohomologySheafOpenIso_unit (n : ℕ) :
    supportRelativeCohomologyToSheaf Y B n ≫
      (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom =
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (supportRelativeCohomologyToSheaf X S n) := by
  change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ _) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    supportOpenEmbeddingSheafificationIso_unit]
  rfl

/-- A genuine section on an auxiliary open ambient space gives a section on its
actual image open in the original ambient space. -/
def supportRelativeCohomologySectionOpenImage (n : ℕ)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op (hf.functor.obj ⊤)) :=
  (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤) s

/-- Restriction of the transported section is transport of its actual restriction. -/
theorem supportRelativeCohomologySectionOpenImage_restrict (n : ℕ)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) (V : Opens Y) :
    (supportRelativeCohomologySheaf X S n).obj.map
      (hf.functor.map (homOfLE (show V ≤ ⊤ from le_top))).op
      (supportRelativeCohomologySectionOpenImage f hf S B hB n s) =
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf Y B n).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op s) :=
  (ConcreteCategory.congr_hom
    ((supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) s).symm

/-- The open transport preserves the literal sheafification images of local classes. -/
theorem supportRelativeCohomologySheafOpenIso_unit_apply (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologyToSheaf Y B n).app (op V) a) =
    (supportRelativeCohomologyToSheaf X S n).app (op (hf.functor.obj V))
      ((supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op V) a) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (supportRelativeCohomologySheafOpenIso_unit f hf S B hB n) (op V)) a
  exact h



/-- Transport to a specified ambient open equal to the actual image. The final
identification is the unique open inclusion, not an arbitrary section equivalence. -/
def supportRelativeCohomologySectionOnOpen (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op U) :=
  (supportRelativeCohomologySheaf X S n).obj.map (eqToHom hU.symm).op
    (supportRelativeCohomologySectionOpenImage f hf S B hB n s)

/-- Restriction to each actual image neighborhood retains the constructed comparison. -/
theorem supportRelativeCohomologySectionOnOpen_restrict (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤))
    (V : Opens Y) (hV : hf.functor.obj V ≤ U) :
    (supportRelativeCohomologySheaf X S n).obj.map (homOfLE hV).op
      (supportRelativeCohomologySectionOnOpen f hf S B hB n U hU s) =
    (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op V)
      ((supportRelativeCohomologySheaf Y B n).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op s) := by
  have he : (eqToHom hU.symm).op ≫ (homOfLE hV).op =
      (hf.functor.map (homOfLE (show V ≤ ⊤ from le_top))).op := Subsingleton.elim _ _
  dsimp only [supportRelativeCohomologySectionOnOpen]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, he]
  exact supportRelativeCohomologySectionOpenImage_restrict f hf S B hB n s V

end AlgebraicTopology.Singular
