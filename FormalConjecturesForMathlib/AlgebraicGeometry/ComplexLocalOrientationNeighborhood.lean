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

public import FormalConjecturesForMathlib.AlgebraicTopology.ChartNeighborhoodOrientation
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexLocalOrientationCoherence

/-!
# Local representability of the exact complex orientation

For every point of a smooth complex scheme, an actual relative singular homology class on an
open neighborhood simultaneously restricts to the prescribed `complexLocalOrientation` at
every point of that neighborhood. The class is constructed from the fixed ordered affine
simplex, transported through the preferred complex chart. Chart coherence identifies its
nearby restrictions with the existing canonical pointwise family.

This proves local representability; it is not a local-representability field or an assumed
orientation of a sheaf. It is the concrete input for gluing the normalized homology-sheaf
orientation.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance complexOrientationNeighborhood_analyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable [SmoothOfRelativeDimension d X.hom]

/-- An open neighborhood carrying a single exactly normalized relative orientation class. -/
def complexLocalOrientationNeighborhood (x : ComplexPoint X) :
    Opens (ComplexPoint X) :=
  chartOrientationNeighborhood d (localChart X d x) x
    (mem_localChart_source X d x)

lemma mem_complexLocalOrientationNeighborhood (x : ComplexPoint X) :
    x ∈ complexLocalOrientationNeighborhood X d x :=
  mem_chartOrientationNeighborhood d (localChart X d x) x
    (mem_localChart_source X d x)

/-- The actual relative singular homology class supported on the constructed neighborhood. -/
def complexLocalOrientationNeighborhoodClass (x : ComplexPoint X) :
    RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
        (complexLocalOrientationNeighborhood X d x : Set (ComplexPoint X))ᶜ)
      (2 * d) :=
  chartOrientationNeighborhoodClass d (localChart X d x) x
    (mem_localChart_source X d x)

/-- Every nearby point restriction is the exact existing complex orientation, with no scalar
ambiguity or arbitrary generator choice. -/
theorem complexLocalOrientationNeighborhoodClass_restrict
    (x y : ComplexPoint X)
    (hy : y ∈ complexLocalOrientationNeighborhood X d x) :
    relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of (ComplexPoint X))
        (Set.singleton_subset_iff.mpr hy))
      (complexLocalOrientationNeighborhoodClass X d x) =
      complexLocalOrientation X d y :=
  (chartOrientationNeighborhoodClass_restrict d (localChart X d x) x
    (mem_localChart_source X d x) y hy).trans
      (complexLocalOrientation_eq_localClassOfChart_localChart X d x y
        (chartOrientationNeighborhood_subset_source d (localChart X d x) x
          (mem_localChart_source X d x) hy)).symm

/-- Simultaneous local representability of the normalized pointwise orientation is a theorem,
witnessed by the explicitly constructed neighborhood-relative class. -/
theorem exists_neighborhood_complexLocalOrientation (x : ComplexPoint X) :
    ∃ (U : Opens (ComplexPoint X)), x ∈ U ∧
      ∃ c : RelativeHomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint X))
          (U : Set (ComplexPoint X))ᶜ) (2 * d),
        ∀ (y : ComplexPoint X) (hy : y ∈ U),
          relativeHomologyMap ℚ (2 * d)
            (supportInclusionPairMap (TopCat.of (ComplexPoint X))
              (Set.singleton_subset_iff.mpr hy)) c =
              complexLocalOrientation X d y :=
  ⟨complexLocalOrientationNeighborhood X d x,
    mem_complexLocalOrientationNeighborhood X d x,
    complexLocalOrientationNeighborhoodClass X d x,
    complexLocalOrientationNeighborhoodClass_restrict X d x⟩

end AlgebraicGeometry.ComplexPoint
