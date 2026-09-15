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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCohomology

/-!
# Singular cohomology over a field

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCohomology`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

@[simp]
lemma cohomologyMap_apply (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (α : Cohomology R Y n) (z : Homology R X n) :
    cohomologyMap R n f α z = α (homologyMap R n f z) :=
  rfl

@[simp]
lemma homologyMap_id (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    homologyMap R n (𝟙 X) = LinearMap.id := by
  change (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
    (ModuleCat.of R R)).map (𝟙 X)).hom = LinearMap.id
  calc
    _ = ModuleCat.Hom.hom (𝟙 (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).obj X)) := congrArg ModuleCat.Hom.hom
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma homologyMap_comp (R : Type u) [Field R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homologyMap R n (f ≫ g) = (homologyMap R n g).comp (homologyMap R n f) := by
  change (((singularHomologyFunctor (ModuleCat.{u} R) n).obj
    (ModuleCat.of R R)).map (f ≫ g)).hom = _
  calc
    _ = ((((singularHomologyFunctor (ModuleCat.{u} R) n).obj
        (ModuleCat.of R R)).map f) ≫
          ((singularHomologyFunctor (ModuleCat.{u} R) n).obj
            (ModuleCat.of R R)).map g).hom := congrArg ModuleCat.Hom.hom
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map_comp f g)
    _ = _ := rfl

@[simp]
lemma cohomologyMap_id (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :
    cohomologyMap R n (𝟙 X) = LinearMap.id := by
  rw [cohomologyMap, homologyMap_id, LinearMap.dualMap_id]

@[simp]
lemma cohomologyMap_comp (R : Type u) [Field R] {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    cohomologyMap R n (f ≫ g) =
      (cohomologyMap R n f).comp (cohomologyMap R n g) := by
  rw [cohomologyMap, cohomologyMap, cohomologyMap, homologyMap_comp,
    LinearMap.dualMap_comp_dualMap]

@[simp]
lemma relativeHomologyMap_id (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    relativeHomologyMap R n (𝟙 X) = LinearMap.id := by
  change ((relativeHomologyFunctor R n).map (𝟙 X)).hom = LinearMap.id
  calc
    _ = ModuleCat.Hom.hom (𝟙 ((relativeHomologyFunctor R n).obj X)) :=
      congrArg ModuleCat.Hom.hom ((relativeHomologyFunctor R n).map_id X)
    _ = LinearMap.id := rfl

@[simp]
lemma relativeHomologyMap_comp (R : Type u) [Field R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeHomologyMap R n (f ≫ g) =
      (relativeHomologyMap R n g).comp (relativeHomologyMap R n f) := by
  change ((relativeHomologyFunctor R n).map (f ≫ g)).hom = _
  calc
    _ = (((relativeHomologyFunctor R n).map f) ≫
        (relativeHomologyFunctor R n).map g).hom :=
      congrArg ModuleCat.Hom.hom ((relativeHomologyFunctor R n).map_comp f g)
    _ = _ := rfl

@[simp]
lemma relativeCohomologyMap_apply (R : Type u) [Field R] {X Y : TopPair.{u}}
    (n : ℕ) (f : X ⟶ Y) (α : RelativeCohomology R Y n)
    (z : RelativeHomology R X n) :
    relativeCohomologyMap R n f α z = α (relativeHomologyMap R n f z) :=
  rfl

@[simp]
lemma relativeCohomologyMap_id (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    relativeCohomologyMap R n (𝟙 X) = LinearMap.id := by
  rw [relativeCohomologyMap, relativeHomologyMap_id, LinearMap.dualMap_id]

@[simp]
lemma relativeCohomologyMap_comp (R : Type u) [Field R] {X Y Z : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    relativeCohomologyMap R n (f ≫ g) =
      (relativeCohomologyMap R n f).comp (relativeCohomologyMap R n g) := by
  rw [relativeCohomologyMap, relativeCohomologyMap, relativeCohomologyMap,
    relativeHomologyMap_comp, LinearMap.dualMap_comp_dualMap]

@[reassoc (attr := simp)]
lemma subspaceChainMap_relativeChainProjection (R : Type u) [Field R]
    (X : TopPair.{u}) :
    ((chainPairFunctor R).obj X).hom ≫ relativeChainProjection R X = 0 :=
  cokernel.condition _

@[simp]
lemma relativeCohomologyToAbsolute_apply (R : Type u) [Field R] (X : TopPair.{u})
    (n : ℕ) (α : RelativeCohomology R X n) (z : Homology R X.fst n) :
    relativeCohomologyToAbsolute R X n α z = α ((relativeHomologyProjection R X n).hom z) :=
  rfl

@[simp]
lemma forgetSupport_apply (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X)
    (n : ℕ) (α : CohomologyWithSupport R X Z n) (z : Homology R X n) :
    forgetSupport R X Z n α z =
      α ((relativeHomologyProjection R (TopPair.ofSubset Zᶜ) n).hom z) :=
  rfl

@[simp]
lemma preimageSupportPairMap_id (X : TopCat.{u}) (Z : Set X) :
    preimageSupportPairMap (𝟙 X) Z = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma preimageSupportPairMap_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Set Z) :
    preimageSupportPairMap (f ≫ g) W =
      preimageSupportPairMap f (g ⁻¹' W) ≫ preimageSupportPairMap g W := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

@[simp]
lemma cohomologyWithSupportMap_apply (R : Type u) [Field R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (Z : Set Y) (α : CohomologyWithSupport R Y Z n)
    (z : RelativeHomology R (TopPair.ofSubset (f ⁻¹' Z)ᶜ) n) :
    cohomologyWithSupportMap R n f Z α z =
      α (relativeHomologyMap R n (preimageSupportPairMap f Z) z) :=
  rfl

@[simp]
lemma cohomologyWithSupportMap_id (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) :
    cohomologyWithSupportMap R n (𝟙 X) Z = LinearMap.id := by
  unfold cohomologyWithSupportMap
  rw [preimageSupportPairMap_id]
  exact relativeCohomologyMap_id R (TopPair.ofSubset Zᶜ) n

lemma cohomologyWithSupportMap_comp (R : Type u) [Field R]
    {X Y Z : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) (W : Set Z) :
    cohomologyWithSupportMap R n (f ≫ g) W =
      (cohomologyWithSupportMap R n f (g ⁻¹' W)).comp
        (cohomologyWithSupportMap R n g W) := by
  rw [cohomologyWithSupportMap, cohomologyWithSupportMap, cohomologyWithSupportMap,
    preimageSupportPairMap_comp, relativeCohomologyMap_comp]

@[simp]
lemma supportInclusionPairMap_rfl (X : TopCat.{u}) (Z : Set X) :
    supportInclusionPairMap X (Set.Subset.rfl : Z ⊆ Z) = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma supportInclusionPairMap_trans (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) :
    supportInclusionPairMap X (hZW.trans hWU) =
      supportInclusionPairMap X hWU ≫ supportInclusionPairMap X hZW := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

@[simp]
lemma enlargeSupport_apply (R : Type u) [Field R] (X : TopCat.{u})
    {Z W : Set X} (h : Z ⊆ W) (n : ℕ) (α : CohomologyWithSupport R X Z n)
    (z : RelativeHomology R (TopPair.ofSubset Wᶜ) n) :
    enlargeSupport R X h n α z =
      α (relativeHomologyMap R n (supportInclusionPairMap X h) z) :=
  rfl

@[simp]
lemma enlargeSupport_rfl (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    enlargeSupport R X (Set.Subset.rfl : Z ⊆ Z) n = LinearMap.id := by
  rw [enlargeSupport, supportInclusionPairMap_rfl, relativeCohomologyMap_id]

lemma enlargeSupport_trans (R : Type u) [Field R] (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) (n : ℕ) :
    enlargeSupport R X (hZW.trans hWU) n =
      (enlargeSupport R X hWU n).comp (enlargeSupport R X hZW n) := by
  rw [enlargeSupport, enlargeSupport, enlargeSupport, supportInclusionPairMap_trans,
    relativeCohomologyMap_comp]

end AlgebraicTopology.Singular
