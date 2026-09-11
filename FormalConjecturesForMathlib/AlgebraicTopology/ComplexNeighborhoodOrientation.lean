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

public import FormalConjecturesForMathlib.AlgebraicTopology.EuclideanNeighborhoodOrientation
public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexOrientation

/-!
# Simultaneous normalized complex-coordinate orientations

The Euclidean neighborhood simplex is transported by the fixed ordered real/imaginary
coordinate homeomorphism. The resulting class has degree `2 * d` and restricts at every point
of its open support to the translation of the exact `standardComplexLocalClass`.

The support-image pair maps used for this transport are actual maps of relative singular
complexes induced by continuous injective maps; their compatibility with point restriction is
proved at the level of maps of topological pairs.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicTopology.Singular

/-- A continuous injective map sends the complement of a support into the complement of its
image, giving an actual covariant map of the relative pairs. -/
def imageSupportPairMap {X Y : TopCat} (f : X ⟶ Y) (hf : Function.Injective f)
    (U : Set X) : TopPair.ofSubset Uᶜ ⟶ TopPair.ofSubset (f '' U)ᶜ := by
  refine TopPair.ofHom f ?_ ?_
  · have hmem : ∀ v : (Uᶜ : Set X), f v.1 ∈ (f '' U)ᶜ := by
      rintro v ⟨w, hw, heq⟩
      exact v.2 ((hf heq) ▸ hw)
    exact TopCat.ofHom ⟨fun v => ⟨f v.1, hmem v⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk hmem⟩
  · rfl

/-- The corresponding map of point-complement pairs. -/
def imagePointPairMap {X Y : TopCat} (f : X ⟶ Y) (hf : Function.Injective f) (x : X) :
    TopPair.ofSubset ({x}ᶜ : Set X) ⟶ TopPair.ofSubset ({f x}ᶜ : Set Y) := by
  refine TopPair.ofHom f ?_ ?_
  · have hmem : ∀ v : ({x}ᶜ : Set X), f v.1 ∈ ({f x}ᶜ : Set Y) := fun v h => v.2 (hf h)
    exact TopCat.ofHom ⟨fun v => ⟨f v.1, hmem v⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk hmem⟩
  · rfl

/-- Transport of support commutes with restriction at an individual point. -/
lemma imageSupportPairMap_restrict {X Y : TopCat} (f : X ⟶ Y)
    (hf : Function.Injective f) (U : Set X) (x : X) (hx : x ∈ U) :
    imageSupportPairMap f hf U ≫
      supportInclusionPairMap Y (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem f hx)) =
      supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx) ≫
        imagePointPairMap f hf x := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext v; rfl
  · rfl

/-- Degree transport commutes with the actual map on relative singular homology. -/
lemma relativeHomologyMap_cast {P Q : TopPair} {m n : ℕ} (h : m = n)
    (f : P ⟶ Q) (c : RelativeHomology ℚ P m) :
    relativeHomologyMap ℚ n f (h ▸ c) = h ▸ relativeHomologyMap ℚ m f c := by
  subst n
  rfl

/-- The fixed inverse real/imaginary coordinate map as a continuous map. -/
def standardRealToComplexMap (d : ℕ) :
    TopCat.of (StandardRealModel (d * 2)) ⟶ TopCat.of (Fin d → ℂ) :=
  TopCat.ofHom ⟨(complexRealHomeomorph d).symm, (complexRealHomeomorph d).symm.continuous⟩

lemma standardRealToComplexMap_injective (d : ℕ) :
    Function.Injective (standardRealToComplexMap d) :=
  (complexRealHomeomorph d).symm.injective

/-- The image of the real orientation ball under the ordered coordinate homeomorphism. -/
def standardComplexOrientationNeighborhood (d : ℕ) : TopologicalSpace.Opens (Fin d → ℂ) :=
  ⟨standardRealToComplexMap d '' (standardOrientationBall (d * 2) : Set _),
    (complexRealHomeomorph d).symm.isOpenMap _ (standardOrientationBall (d * 2)).isOpen⟩

lemma zero_mem_standardComplexOrientationNeighborhood (d : ℕ) :
    (0 : Fin d → ℂ) ∈ standardComplexOrientationNeighborhood d := by
  refine ⟨0, zero_mem_standardOrientationBall (d * 2), ?_⟩
  exact map_zero (Complex.piCoordCLE d).symm

/-- The complex-coordinate neighborhood pair supporting the oriented simplex. -/
abbrev standardComplexOrientationNeighborhoodPair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin d → ℂ))
    (standardComplexOrientationNeighborhood d : Set (Fin d → ℂ))ᶜ

/-- The normalized complex neighborhood class. The only degree cast is the proved arithmetic
identity `d * 2 = 2 * d` converting the ordered real-coordinate dimension. -/
def standardComplexOrientationNeighborhoodClass (d : ℕ) :
    RelativeHomology ℚ (standardComplexOrientationNeighborhoodPair d) (2 * d) :=
  (Nat.mul_comm d 2) ▸
    relativeHomologyMap ℚ (d * 2)
      (imageSupportPairMap (standardRealToComplexMap d) (standardRealToComplexMap_injective d)
        (standardOrientationBall (d * 2))) (standardOrientationBallClass (d * 2))

/-- The ordered coordinate map commutes exactly with translations, including the maps on
punctured subspaces. -/
lemma standardRealToComplexPair_translation (d : ℕ) (v : StandardRealModel (d * 2)) :
    translationPointComplementPairMap (StandardRealModel (d * 2)) v ≫
      imagePointPairMap (standardRealToComplexMap d) (standardRealToComplexMap_injective d) v =
      standardRealToComplexPair d ≫
        translationPointComplementPairMap (Fin d → ℂ) (standardRealToComplexMap d v) := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    refine Subtype.ext ?_
    exact map_add (Complex.piCoordCLE d).symm _ _
  · ext w
    exact map_add (Complex.piCoordCLE d).symm _ _

set_option backward.isDefEq.respectTransparency false in
/-- Throughout the complex-coordinate neighborhood the same relative class restricts to the
exact translate of the prescribed complex orientation. -/
theorem standardComplexOrientationNeighborhoodClass_restrict (d : ℕ) (y : Fin d → ℂ)
    (hy : y ∈ standardComplexOrientationNeighborhood d) :
    relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr hy))
      (standardComplexOrientationNeighborhoodClass d) =
      relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) y)
        (standardComplexLocalClass d) := by
  obtain ⟨v, hv, rfl⟩ := hy
  rw [standardComplexOrientationNeighborhoodClass, relativeHomologyMap_cast]
  change (Nat.mul_comm d 2) ▸ relativeHomologyMap ℚ (d * 2) _
      (relativeHomologyMap ℚ (d * 2) _ (standardOrientationBallClass (d * 2))) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    imageSupportPairMap_restrict _ _ _ _ hv,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    show supportInclusionPairMap (TopCat.of (StandardRealModel (d * 2)))
        (Set.singleton_subset_iff.mpr hv) = standardOrientationBallPointMap (d * 2) v hv from rfl,
    standardOrientationBallClass_restrict, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, standardRealToComplexPair_translation,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  change (Nat.mul_comm d 2) ▸ relativeHomologyMap ℚ (d * 2) _
      ((standardComplexRealRelativeHomologyIso d).inv.hom (standardLocalClass (d * 2))) = _
  exact (relativeHomologyMap_cast (Nat.mul_comm d 2) _ _).symm

end AlgebraicTopology.Singular
