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

public import FormalConjecturesForMathlib.AlgebraicTopology.NormalProjectionCoclass
public import FormalConjecturesForMathlib.AlgebraicTopology.SheafMapOfLocallyRepresentableStalks

/-!
# The actual local relative-cohomology presheaf and its sheafification

For a support `S ⊆ X`, the value on `V` is the rational relative cohomology of
the actual pair `(V, V \ S)`, viewed as an additive group. Restrictions are
the pullbacks along literal inclusions of these pairs. The sheaf is its actual
sheafification. This module also proves local vanishing away from closed support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex
open TopCat.Presheaf

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

@[simp] theorem neighborhoodSupportInclusionPairMap_id (W S : Set M) :
    neighborhoodSupportInclusionPairMap (show W ⊆ W from le_refl W) S =
      𝟙 (neighborhoodSupportComplementPair W S) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

@[simp] theorem neighborhoodSupportInclusionPairMap_comp {U V W : Set M}
    (hUV : U ⊆ V) (hVW : V ⊆ W) (S : Set M) :
    neighborhoodSupportInclusionPairMap hUV S ≫ neighborhoodSupportInclusionPairMap hVW S =
      neighborhoodSupportInclusionPairMap (hUV.trans hVW) S := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

variable (X : TopCat.{0}) (S : Set X) (n : ℕ)

/-- The literal presheaf of rational relative cohomology of neighborhood/support pairs.
We retain the rational group but forget its scalar structure for the additive sheaf API. -/
def supportRelativeCohomologyPresheaf : TopCat.Presheaf AddCommGrpCat X where
  obj V := AddCommGrpCat.of (RelativeCohomology ℚ
    (neighborhoodSupportComplementPair (V.unop : Set X) S) n)
  map {U V} f := AddCommGrpCat.ofHom
    (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
      (W := (V.unop : Set X)) (V := (U.unop : Set X)) (leOfHom f.unop) S)).toAddMonoidHom
  map_id V := by
    change AddCommGrpCat.ofHom
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (show (V.unop : Set X) ⊆ V.unop from le_refl _) S)).toAddMonoidHom = _
    rw [neighborhoodSupportInclusionPairMap_id, relativeCohomologyMap_id]
    rfl
  map_comp {U V W} f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (W.unop : Set X)) (V := (U.unop : Set X))
        (leOfHom (f ≫ g).unop) S) a =
        relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
          (W := (W.unop : Set X)) (V := (V.unop : Set X)) (leOfHom g.unop) S)
          (relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap
            (W := (V.unop : Set X)) (V := (U.unop : Set X)) (leOfHom f.unop) S) a)
    rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, neighborhoodSupportInclusionPairMap_comp]

@[simp] theorem supportRelativeCohomologyPresheaf_map_apply {U V : Opens X}
    (hUV : U ≤ V) (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    (supportRelativeCohomologyPresheaf X S n).map (homOfLE hUV).op a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a := rfl

/-- Actual sheafification, not a presupposed sheaf property of relative cohomology. -/
def supportRelativeCohomologySheaf : TopCat.Sheaf AddCommGrpCat X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (supportRelativeCohomologyPresheaf X S n)

/-- The canonical map taking an actual relative class to its sheafified local section. -/
def supportRelativeCohomologyToSheaf :
    supportRelativeCohomologyPresheaf X S n ⟶ (supportRelativeCohomologySheaf X S n).obj :=
  toSheafify (Opens.grothendieckTopology X) _

/-- Germ of an actual relative coclass in the sheafification. -/
def supportRelativeCohomologyGerm (V : Opens X) (x : X) (hx : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    (supportRelativeCohomologySheaf X S n).presheaf.stalk x :=
  (supportRelativeCohomologySheaf X S n).presheaf.germ V x hx
    ((supportRelativeCohomologyToSheaf X S n).app (op V) a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction followed by germ is the original germ; the restriction is the
literal pair-inclusion pullback. -/
theorem supportRelativeCohomologyGerm_restrict {U V : Opens X} (hUV : U ≤ V)
    (x : X) (hx : x ∈ U)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    supportRelativeCohomologyGerm X S n U x hx
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (U : Set X)) (V := (V : Set X)) hUV S) a) =
    supportRelativeCohomologyGerm X S n V x (hUV hx) a := by
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S n).naturality (homOfLE hUV).op) a
  simp only [ConcreteCategory.comp_apply] at h
  exact (congrArg ((supportRelativeCohomologySheaf X S n).presheaf.germ U x hx) h).trans
    ((supportRelativeCohomologySheaf X S n).presheaf.germ_res_apply (homOfLE hUV) x hx _)

/-- Equality after actual restriction to a common neighborhood gives equal sheaf germs. -/
theorem supportRelativeCohomologyGerm_eq_of_restrict_eq
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) (x : X) (hx : x ∈ W)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (U : Set X)) hWU S) a =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) b) :
    supportRelativeCohomologyGerm X S n U x (hWU hx) a =
      supportRelativeCohomologyGerm X S n V x (hWV hx) b := by
  rw [← supportRelativeCohomologyGerm_restrict X S n hWU x hx,
    ← supportRelativeCohomologyGerm_restrict X S n hWV x hx, h]

/-- When a neighborhood misses the support, its actual relative-chain complex is zero. -/
theorem neighborhoodSupportRelativeChains_isZero (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    IsZero ((relativeChainFunctor ℚ).obj (neighborhoodSupportComplementPair V S)) := by
  have hset : {v : V | v.1 ∉ S} = Set.univ := Set.eq_univ_of_forall fun v => hV v.1 v.2
  change IsZero ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := TopCat.of V) _))
  rw [hset]
  let P := TopPair.ofSubset (X := TopCat.of V) (Set.univ : Set V)
  have hPi : IsIso P.map :=
    (TopCat.isIso_iff_isHomeomorph P.map).mpr (Homeomorph.Set.univ V).isHomeomorph
  have hchain : IsIso ((chainPairFunctor ℚ).obj P).hom := by
    change IsIso (((singularChainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map P.map)
    infer_instance
  exact isZero_cokernel_of_epi ((chainPairFunctor ℚ).obj P).hom

/-- Relative cohomology vanishes on neighborhoods disjoint from the support. -/
theorem neighborhoodSupportRelativeCohomology_subsingleton
    (V : Set X) (hV : ∀ x ∈ V, x ∉ S) :
    Subsingleton (RelativeCohomology ℚ (neighborhoodSupportComplementPair V S) n) := by
  have hh : IsZero (RelativeHomology ℚ (neighborhoodSupportComplementPair V S) n) :=
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero
      (neighborhoodSupportRelativeChains_isZero X S V hV)
  let := ModuleCat.subsingleton_of_isZero hh
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Off closed support, every actual local relative class has zero sheaf germ. -/
theorem supportRelativeCohomologyGerm_eq_zero_of_not_mem (hS : IsClosed S)
    (V : Opens X) (x : X) (hx : x ∈ V) (hxS : x ∉ S)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n) :
    supportRelativeCohomologyGerm X S n V x hx a = 0 := by
  let W : Opens X := V ⊓ ⟨Sᶜ, hS.isOpen_compl⟩
  have hWV : W ≤ V := inf_le_left
  have hxW : x ∈ W := ⟨hx, hxS⟩
  let := neighborhoodSupportRelativeCohomology_subsingleton X S n W (fun _ hy => hy.2)
  rw [← supportRelativeCohomologyGerm_restrict X S n hWV x hxW]
  have hz : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (W := (W : Set X)) (V := (V : Set X)) hWV S) a = 0 :=
    Subsingleton.elim _ _
  rw [hz]
  simp only [supportRelativeCohomologyGerm, map_zero]

end AlgebraicTopology.Singular
