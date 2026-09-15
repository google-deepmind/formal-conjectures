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

public import FormalConjecturesForMathlib.Mathlib.Algebra.Category.ModuleCat.Basic -- shake: keep
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

/-- Relative singular cohomology over a field. -/
abbrev RelativeCohomology (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :=
  Module.Dual R (RelativeHomology R X n)

/-- Pullback in relative singular cohomology. -/
def relativeCohomologyMap (R : Type u) [Field R] {X Y : TopPair.{u}} (n : ℕ)
    (f : X ⟶ Y) : RelativeCohomology R Y n →ₗ[R] RelativeCohomology R X n :=
  (relativeHomologyMap R n f).dualMap

/-- The quotient map from absolute singular chains of `X` to relative chains of `(X, A)`. -/
def relativeChainProjection (R : Type u) [Field R] (X : TopPair.{u}) :
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X.fst ⟶
      (relativeChainFunctor R).obj X :=
  cokernel.π ((chainPairFunctor R).obj X).hom

/-- The quotient map from absolute homology to relative homology. -/
def relativeHomologyProjection (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    Homology R X.fst n ⟶ RelativeHomology R X n :=
  HomologicalComplex.homologyMap (relativeChainProjection R X) n

/-- The canonical map from relative cohomology to absolute cohomology. -/
def relativeCohomologyToAbsolute (R : Type u) [Field R] (X : TopPair.{u}) (n : ℕ) :
    RelativeCohomology R X n →ₗ[R] Cohomology R X.fst n :=
  (relativeHomologyProjection R X n).hom.dualMap

/-- Singular cohomology of `X` with support in `Z`, defined as `H^n(X, X ∖ Z)`. -/
abbrev CohomologyWithSupport (R : Type u) [Field R] (X : TopCat.{u})
    (Z : Set X) (n : ℕ) :=
  RelativeCohomology R (TopPair.ofSubset Zᶜ) n

/-- Forget support in `Z`, mapping a supported class to ordinary singular cohomology. -/
def forgetSupport (R : Type u) [Field R] (X : TopCat.{u}) (Z : Set X) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] Cohomology R X n :=
  relativeCohomologyToAbsolute R (TopPair.ofSubset Zᶜ) n

/-- A continuous map, regarded as a map of pairs for a closed support and its preimage. -/
def preimageSupportPairMap {X Y : TopCat.{u}} (f : X ⟶ Y) (Z : Set Y) :
    TopPair.ofSubset (f ⁻¹' Z)ᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom f
    (TopCat.ofHom ⟨fun x => ⟨f x.1, x.2⟩,
      Continuous.subtype_mk (f.hom.continuous.comp continuous_subtype_val) _⟩)
    (by ext x; rfl)

/-- Pull back a supported cohomology class. Its support pulls back along the continuous map. -/
def cohomologyWithSupportMap (R : Type u) [Field R] {X Y : TopCat.{u}}
    (n : ℕ) (f : X ⟶ Y) (Z : Set Y) :
    CohomologyWithSupport R Y Z n →ₗ[R]
      CohomologyWithSupport R X (f ⁻¹' Z) n :=
  relativeCohomologyMap R n (preimageSupportPairMap f Z)

/-- The identity map as a map of pairs for an inclusion of supports `Z ⊆ W`. -/
def supportInclusionPairMap (X : TopCat.{u}) {Z W : Set X} (h : Z ⊆ W) :
    TopPair.ofSubset Wᶜ ⟶ TopPair.ofSubset Zᶜ :=
  TopPair.ofHom (𝟙 X)
    (TopCat.ofHom ⟨fun x => ⟨x.1, fun hx => x.2 (h hx)⟩, by fun_prop⟩)
    (by ext x; rfl)

/-- Enlarge the allowed support of a supported cohomology class. -/
def enlargeSupport (R : Type u) [Field R] (X : TopCat.{u}) {Z W : Set X}
    (h : Z ⊆ W) (n : ℕ) :
    CohomologyWithSupport R X Z n →ₗ[R] CohomologyWithSupport R X W n :=
  relativeCohomologyMap R n (supportInclusionPairMap X h)

end AlgebraicTopology.Singular
