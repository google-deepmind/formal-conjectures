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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenSheafRestriction
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Sheafification commutes with actual open restriction

Open-image functors lift covering sieves. The resulting sheafification
comparison is the actual sheafification lift of the restricted unit.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

/-- Covering sieves on an open image pull back to covering sieves in the
open subspace. -/
lemma functor_isCocontinuous :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) where
  cover_lift {U S} hS x hx := by
    obtain ⟨V, i, hV, hxV⟩ := hS (f x) ⟨x, hx, rfl⟩
    let V' := (Opens.map f).obj V
    have hle : V' ≤ U := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := i.le hy
      exact hf.injective hzy ▸ hz
    exact ⟨V', homOfLE hle, S.downward_closed hV (homOfLE (Set.image_preimage_subset f V)), hxV⟩

end Topology.IsOpenEmbedding

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sheafification followed by actual open restriction is canonically
sheafification of the restricted presheaf. -/
def openRestrictionSheafificationIso (P : Presheaf AddCommGrpCat.{u} X) :
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj
      (U.isOpenEmbedding.functor.op ⋙ P) ≅
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj P) := by
  let : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isContinuous
  let : U.isOpenEmbedding.functor.IsCocontinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isCocontinuous
  exact (U.isOpenEmbedding.functor.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology X)).app P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison is normalized by the actual restricted sheafification
unit, so no independently selected stalk or section isomorphism is used. -/
@[reassoc]
lemma toSheafify_openRestrictionSheafificationIso (P : Presheaf AddCommGrpCat.{u} X) :
    toSheafify (Opens.grothendieckTopology (TopCat.of U))
        (U.isOpenEmbedding.functor.op ⋙ P) ≫
      (openRestrictionSheafificationIso X U P).hom.hom =
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X) P) := by
  let : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isContinuous
  let : U.isOpenEmbedding.functor.IsCocontinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isCocontinuous
  exact U.isOpenEmbedding.functor.toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology X) P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma openRestrictionSheafificationIso_naturality
    {P Q : Presheaf AddCommGrpCat.{u} X} (f : P ⟶ Q) :
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).map
        (Functor.whiskerLeft U.isOpenEmbedding.functor.op f) ≫
      (openRestrictionSheafificationIso X U Q).hom =
    (openRestrictionSheafificationIso X U P).hom ≫
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map f) := by
  let : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isContinuous
  let : U.isOpenEmbedding.functor.IsCocontinuous
      (Opens.grothendieckTopology (TopCat.of U)) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isCocontinuous
  exact (U.isOpenEmbedding.functor.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology (TopCat.of U))
      (Opens.grothendieckTopology X)).hom.naturality f

end TopCat.Sheaf
