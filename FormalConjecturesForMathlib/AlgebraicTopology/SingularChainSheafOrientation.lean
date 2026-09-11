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

public import FormalConjecturesForMathlib.AlgebraicTopology.DerivedConcentratedOrientation
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularChainHomologySheaf

/-!
# From local singular homology to the derived orientation

This is the canonical truncation bridge for the *actual* relative singular-chain sheaf.
Its two explicit mathematical hypotheses are local homology vanishing outside degree
`N`, and an orientation of the actual degree-`N` homology sheaf. The latter is not an
arbitrary derived equivalence: the derived comparison is constructed, and the general
normalization theorem proves that it induces exactly the given sheaf orientation.

For complex dimension `d`, take `N = 2*d`; homological degree `N` is cohomological degree
`-N`, so the resulting orientation is `ω ≅ R_X[N]`. Local vanishing and the normalized
orientation of the homology sheaf must still be established geometrically. This module
does not claim Verdier duality or the intrinsic Borel--Moore comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Reindexing the actual homology sheaf from homological to cohomological grading. -/
def singularChainSheafCochainHomologyIso (N : ℕ) :
    (singularChainSheafCochainComplex R X).homology (-(N : ℤ)) ≅
      singularChainHomologySheaf R X N :=
  (singularChainSheafComplex R X).extendHomologyIso ComplexShape.embeddingDownNat rfl

/-- Local relative homology concentration implies cohomological concentration of the
actual chain-sheaf complex. Positive degrees vanish because the complex is termwise
bounded above by zero. -/
theorem singularChainSheafCochainHomology_concentrated [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    ∀ i : ℤ, i ≠ -(N : ℤ) →
      IsZero ((singularChainSheafCochainComplex R X).homology i) := by
  intro i hi
  by_cases hpos : 0 < i
  · exact (singularChainSheafCochainComplex R X).isZero_of_isLE 0 i hpos
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = -(m : ℤ) := ⟨(-i).toNat, by omega⟩
    exact (singularChainSheafCochainHomologyIso R X m).isZero_iff.mpr
      (singularChainHomologySheaf_isZero_of_localHomology_isZero R X m
        (hlocal m (by omega)))

/-- The constant coefficient sheaf on an arbitrary topological space. -/
abbrev singularOrientationConstantSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of R)

local instance singularChainSheafOrientationHasDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

/-- The unshifted form of the canonical orientation, used to state its normalization
without obscuring the surviving homology degree by shift comparison maps. -/
def singularChainSheafDerivedSingleOrientationIso [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (orientation : singularChainHomologySheaf R X N ≅
      singularOrientationConstantSheaf R X) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex R X) ≅
      (DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} X) (-(N : ℤ))).obj
        (singularOrientationConstantSheaf R X) :=
  DerivedCategory.concentratedOrientationIso (singularChainSheafCochainComplex R X)
    (-(N : ℤ)) (singularChainSheafCochainHomology_concentrated R X N hlocal)
    (singularChainSheafCochainHomologyIso R X N ≪≫ orientation)

/-- On top homology the derived orientation is exactly the given sheaf orientation,
preceded only by the canonical homological/cohomological reindexing comparison. -/
@[reassoc]
theorem singularChainSheafDerivedSingleOrientationIso_homology [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (orientation : singularChainHomologySheaf R X N ≅
      singularOrientationConstantSheaf R X) :
    (DerivedCategory.homologyFunctor _ (-(N : ℤ))).map
      (singularChainSheafDerivedSingleOrientationIso R X N hlocal orientation).hom ≫
      (DerivedCategory.homologyFunctorFactors _ (-(N : ℤ))).hom.app
        ((single _ (.up ℤ) (-(N : ℤ))).obj (singularOrientationConstantSheaf R X)) ≫
      (singleObjHomologySelfIso (.up ℤ) (-(N : ℤ)) _).hom =
      (DerivedCategory.homologyFunctorFactors _ (-(N : ℤ))).hom.app
        (singularChainSheafCochainComplex R X) ≫
        (singularChainSheafCochainHomologyIso R X N).hom ≫ orientation.hom :=
  DerivedCategory.concentratedOrientationIso_homology _ _ _ _

/-- Canonical derived orientation of the actual relative-chain sheaf, obtained from
local homology concentration and the specified orientation of its homology sheaf. -/
def singularChainSheafDerivedOrientationIso [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m))
    (orientation : singularChainHomologySheaf R X N ≅
      singularOrientationConstantSheaf R X) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex R X) ≅
      ((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat.{u} X) 0).obj
        (singularOrientationConstantSheaf R X))⟦(N : ℤ)⟧ := by
  simpa only [neg_neg] using DerivedCategory.concentratedOrientationShiftIso
    (singularChainSheafCochainComplex R X) (-(N : ℤ))
    (singularChainSheafCochainHomology_concentrated R X N hlocal)
    (singularChainSheafCochainHomologyIso R X N ≪≫ orientation)

/-- Cohomological concentration constructs the `D⁺` object of the actual chain sheaf.
No termwise bounded-below hypothesis or replacement complex is supplied. -/
def singularChainSheafPlusObject [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  DerivedCategory.concentratedPlusObject (singularChainSheafCochainComplex R X)
    (-(N : ℤ)) (singularChainSheafCochainHomology_concentrated R X N hlocal)

/-- The `D⁺` object is literally the localization of the actual relative-chain model. -/
@[simp]
theorem singularChainSheafPlusObject_obj [T2Space X] (N : ℕ)
    (hlocal : ∀ (m : ℕ), m ≠ N → ∀ x : X,
      IsZero (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) m)) :
    DerivedCategory.Plus.ι.obj (singularChainSheafPlusObject R X N hlocal) =
      DerivedCategory.Q.obj (singularChainSheafCochainComplex R X) := rfl

end AlgebraicTopology.Singular
