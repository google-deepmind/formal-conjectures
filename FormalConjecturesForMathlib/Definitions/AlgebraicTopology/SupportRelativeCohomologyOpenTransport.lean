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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SupportRelativeCohomologySheaf
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.NeighborhoodSupportPairImage
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenSheafification

/-!
# Open-embedding transport of the relative-cohomology sheaf

The embedding homeomorphisms identify neighborhood/support pairs with their images, and
these identifications commute with pair inclusions, giving a presheaf isomorphism.
Sheafification then transports the normalized section, with the sheafification-unit
square displayed.
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
    ext a
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

/-- Actual sheafification of the pair comparison identifies intrinsic local support
cohomology with restriction of the original ambient relative-cohomology sheaf. -/
def supportRelativeCohomologySheafOpenIso (n : ℕ) :
    supportRelativeCohomologySheaf Y B n ≅
      (hf.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf X S n) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).mapIso
      (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).symm ≪≫
    supportOpenEmbeddingSheafificationIso f hf (supportRelativeCohomologyPresheaf X S n)

/-- A genuine section on an auxiliary open ambient space gives a section on its
actual image open in the original ambient space. -/
def supportRelativeCohomologySectionOpenImage (n : ℕ)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op (hf.functor.obj ⊤)) :=
  (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom.app (op ⊤) s

/-- Transport to a specified ambient open equal to the actual image. The final
identification is the unique open inclusion, not an arbitrary section equivalence. -/
def supportRelativeCohomologySectionOnOpen (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) :
    (supportRelativeCohomologySheaf X S n).obj.obj (op U) :=
  (supportRelativeCohomologySheaf X S n).obj.map (eqToHom hU.symm).op
    (supportRelativeCohomologySectionOpenImage f hf S B hB n s)

end AlgebraicTopology.Singular
