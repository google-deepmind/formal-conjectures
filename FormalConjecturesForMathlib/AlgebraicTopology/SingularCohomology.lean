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

public import FormalConjecturesForMathlib.Algebra.Category.ModuleCat.Basic -- shake: keep
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits -- shake: keep
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Category.TopPair

/-!
# Singular cohomology over a field

This file constructs field-valued singular cohomology from Mathlib's singular chain complex.
Over a field, the universal coefficient theorem canonically identifies cohomology with the linear
dual of homology, so this description avoids a noncanonical choice of representatives.

For a topological pair `A ⊆ X`, the relative chain complex is the cokernel of the actual chain map
`C_*(A) ⟶ C_*(X)`. Relative cohomology, cohomology with support, and the map that forgets support
are derived from this construction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

/-- Singular homology of a topological space with coefficients in a field. -/
abbrev Homology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} R :=
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj X

/-- Singular cohomology with coefficients in a field, using the universal-coefficient
identification with the linear dual of singular homology. -/
abbrev Cohomology (R : Type u) [Field R] (X : TopCat.{u}) (n : ℕ) :=
  Module.Dual R (Homology R X n)

/-- The map on singular homology induced by a continuous map. -/
def homologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Homology R X n →ₗ[R] Homology R Y n :=
  (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map f).hom

/-- Pullback in singular cohomology. -/
def cohomologyMap (R : Type u) [Field R] {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) :
    Cohomology R Y n →ₗ[R] Cohomology R X n :=
  (homologyMap R n f).dualMap

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

/-- The category containing field-valued singular chain complexes. -/
abbrev ChainCategory (R : Type u) [Field R] :=
  ChainComplex (ModuleCat.{u} R) ℕ

/-- A topological pair `A ⊆ X`, sent to the induced arrow `C_*(A) ⟶ C_*(X)` of singular
chain complexes. -/
def chainPairFunctor (R : Type u) [Field R] :
    TopPair.{u} ⥤ Arrow (ChainCategory R) where
  __ := MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤ ⋙
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapArrow

/-- The relative singular chain complex `C_*(X, A)`, defined as the cokernel of
`C_*(A) ⟶ C_*(X)`. -/
def relativeChainFunctor (R : Type u) [Field R] :
    TopPair.{u} ⥤ ChainCategory R :=
  chainPairFunctor R ⋙ Limits.coker (C := ChainCategory R)

/-- Relative singular homology. -/
def relativeHomologyFunctor (R : Type u) [Field R] (n : ℕ) :
    TopPair.{u} ⥤ ModuleCat.{u} R :=
  relativeChainFunctor R ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Relative singular homology of the pair `A ⊆ X`. -/
abbrev RelativeHomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    ModuleCat.{u} R :=
  (relativeHomologyFunctor R n).obj X

/-- The map on relative homology induced by a map of pairs. -/
def relativeHomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeHomology R X n →ₗ[R] RelativeHomology R Y n :=
  ((relativeHomologyFunctor R n).map f).hom

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

/-- Relative singular cohomology over a field. -/
abbrev RelativeCohomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :=
  Module.Dual R (RelativeHomology R X n)

/-- Pullback in relative singular cohomology. -/
def relativeCohomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeCohomology R Y n →ₗ[R] RelativeCohomology R X n :=
  (relativeHomologyMap R n f).dualMap

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

/-- The quotient map from absolute singular chains of `X` to relative chains of `(X, A)`. -/
def relativeChainProjection (R : Type u) [Field R] (X : TopPair.{u}) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X.fst ⟶
      (relativeChainFunctor R).obj X :=
  cokernel.π ((chainPairFunctor R).obj X).hom

@[reassoc (attr := simp)]
lemma subspaceChainMap_relativeChainProjection (R : Type u) [Field R]
    (X : TopPair.{u}) :
    ((chainPairFunctor R).obj X).hom ≫ relativeChainProjection R X = 0 :=
  cokernel.condition _

/-- The quotient map from absolute homology to relative homology. -/
def relativeHomologyProjection (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    Homology R X.fst n ⟶ RelativeHomology R X n :=
  HomologicalComplex.homologyMap (relativeChainProjection R X) n

/-- The canonical map from relative cohomology to absolute cohomology. -/
def relativeCohomologyToAbsolute (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n →ₗ[R] Cohomology R X.fst n :=
  (relativeHomologyProjection R X n).hom.dualMap

@[simp]
lemma relativeCohomologyToAbsolute_apply (R : Type u) [Field R] (X : TopPair.{u})
    (n : ℕ) (α : RelativeCohomology R X n) (z : Homology R X.fst n) :
    relativeCohomologyToAbsolute R X n α z = α ((relativeHomologyProjection R X n).hom z) :=
  rfl

/-- Singular cohomology of `X` with support in `Z`, defined as `H^n(X, X ∖ Z)`. -/
abbrev CohomologyWithSupport (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) :=
  RelativeCohomology R (TopPair.ofSubset Zᶜ) n

/-- Forget support in `Z`, mapping a supported class to ordinary singular cohomology. -/
def forgetSupport (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] Cohomology R X n :=
  relativeCohomologyToAbsolute R (TopPair.ofSubset Zᶜ) n

@[simp]
lemma forgetSupport_apply (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X)
    (n : ℕ) (α : CohomologyWithSupport R X Z n) (z : Homology R X n) :
    forgetSupport R X Z n α z =
      α ((relativeHomologyProjection R (TopPair.ofSubset Zᶜ) n).hom z) :=
  rfl

/-- A continuous map, regarded as a map of pairs for a closed support and its preimage. -/
def preimageSupportPairMap {X Y : TopCat.{u}} (f : X ⟶ Y) (Z : Set Y) :
    TopPair.ofSubset (f ⁻¹' Z)ᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun x => ⟨f x.1, x.2⟩,
      Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩)
    (by ext x; rfl)

@[simp]
lemma preimageSupportPairMap_id (X : TopCat.{u}) (Z : Set X) :
    preimageSupportPairMap (𝟙 X) Z = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma preimageSupportPairMap_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : Set Z) :
    preimageSupportPairMap (f ≫ g) W =
      preimageSupportPairMap f (g ⁻¹' W) ≫ preimageSupportPairMap g W := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Pull back a supported cohomology class. Its support pulls back along the continuous map. -/
def cohomologyWithSupportMap (R : Type u) [Field R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (Z : Set Y) :
    CohomologyWithSupport R Y Z n →ₗ[R]
      CohomologyWithSupport R X (f ⁻¹' Z) n :=
  relativeCohomologyMap R n (preimageSupportPairMap f Z)

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

/-- The identity map as a map of pairs for an inclusion of supports `Z ⊆ W`. -/
def supportInclusionPairMap (X : TopCat.{u}) {Z W : Set X} (h : Z ⊆ W) :
    TopPair.ofSubset Wᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom (𝟙 X)
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h hx)⟩,
      continuous_subtype_val.subtype_mk _⟩)
    (by ext x; rfl)

@[simp]
lemma supportInclusionPairMap_rfl (X : TopCat.{u}) (Z : Set X) :
    supportInclusionPairMap X (Set.Subset.rfl : Z ⊆ Z) = 𝟙 (TopPair.ofSubset Zᶜ) := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

lemma supportInclusionPairMap_trans (X : TopCat.{u}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) :
    supportInclusionPairMap X (hZW.trans hWU) =
      supportInclusionPairMap X hWU ≫ supportInclusionPairMap X hZW := by
  apply MorphismProperty.Arrow.Hom.ext <;> rfl

/-- Enlarge the allowed support of a supported cohomology class. -/
def enlargeSupport (R : Type u) [Field R] (X : TopCat.{u}) {Z W : Set X}
    (h : Z ⊆ W) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] CohomologyWithSupport R X W n :=
  relativeCohomologyMap R n (supportInclusionPairMap X h)

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
