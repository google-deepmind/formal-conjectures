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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SupportRelativeCohomologyOpenTransport

/-!
# Actual open-embedding transport of the relative-cohomology sheaf

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SupportRelativeCohomologyOpenTransport`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace AlgebraicTopology.Singular

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- Literal pair pullback is the forward component of the constructed equivalence. -/
theorem neighborhoodSupportPairImageCohomologyEquiv_apply (V : Opens Y) (n : ℕ)
    (a : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (hf.functor.obj V : Set X) S) n) :
    neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding (V : Set Y) B S
      (fun y _ => by rw [← hB]; rfl) n a =
    relativeCohomologyMap ℚ n
      (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
        (fun y _ => by rw [← hB]; rfl)).hom a := rfl

/-- Inverse transport is literal pullback along the inverse pair homeomorphism. -/
theorem supportRelativeCohomologyPresheafOpenIso_inv_app (n : ℕ) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n) :
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv.app (op V) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).inv a := rfl

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
