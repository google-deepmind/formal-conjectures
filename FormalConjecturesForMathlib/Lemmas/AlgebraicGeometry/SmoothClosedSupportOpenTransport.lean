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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ClosedImmersionSourceOpen
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.NeighborhoodSupportPairImage

/-!
# Local purity neighborhoods transported out of ambient opens

The normal-neighborhood construction uses smooth geometry alone. This module transports
its support pairs along an open embedding, so cohomology can still be computed with a
resolution on the original ambient space. The support-membership identity is purely
topological.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- Actual normal neighborhoods can be computed in any smooth auxiliary ambient open
and then transported to the original topological ambient space. -/
theorem exists_smoothClosedSupportImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint X → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (z : ComplexPoint Y) (V : Opens M) (hzV : f (Point.map i z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧ f (Point.map i z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint X) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  let W' := smoothClosedSupportNeighborhood X Y i m d z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint X)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact smoothClosedSupportNeighborhood_le X Y i m d z V' hzV hw
  · exact ⟨_, mem_smoothClosedSupportNeighborhood X Y i m d z V' hzV, rfl⟩
  · intro n hn
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W' : Set (ComplexPoint X))
          (Set.range (Point.map i))) n) :=
      ModuleCat.subsingleton_of_isZero
        (smoothClosedSupportRelativeCohomology_isZero_of_ne X Y i m d z V' hzV n hn)
    let e := neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (Point.map i)) S (fun w _ => by
        rw [← hS]
        rfl) n
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

omit [SmoothOfRelativeDimension m Y.hom] in
/-- Fixed-dimensional source opens suffice: the target is restricted by deleting the
discarded closed image, while the resulting neighborhoods and pairs live in the original
ambient analytic space. No projectivity or global source dimension is needed. -/
theorem exists_smoothClosedSourceOpenNeighborhood
    (A : Y.left.Opens) [SmoothOfRelativeDimension m (openScheme Y A).hom]
    (z : ComplexPoint (openScheme Y A))
    (V : Opens (ComplexPoint X))
    (hzV : Point.map (openInclusion Y A ≫ i) z ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧
      Point.map (openInclusion Y A ≫ i) z ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
            (Set.range (Point.map i))) n)) := by
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  let T := closedImmersionSourceOpenTarget i.left A
  let j := closedImmersionSourceOpenLift i.left A
  have hj : j ≫ (openScheme X T).hom = (openScheme Y A).hom := by
    change j ≫ (T.ι ≫ X.hom) = A.ι ≫ Y.hom
    rw [← Category.assoc, closedImmersionSourceOpenLift_ι, Category.assoc, i.w]
  let jOver : openScheme Y A ⟶ openScheme X T := Over.homMk j hj
  let : IsClosedImmersion jOver.left :=
    closedImmersionSourceOpenLift_isClosedImmersion i.left A
  have : SmoothOfRelativeDimension d (openScheme X T).hom := by
    change SmoothOfRelativeDimension d (T.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d T.ι X.hom
  have : Smooth (openScheme X T).hom :=
    SmoothOfRelativeDimension.smooth d (openScheme X T).hom
  let f := Point.map (openInclusion X T)
  have hS : f ⁻¹' Set.range (Point.map i) = Set.range (Point.map jOver) := by
    rw [range_map_of_isImmersion_of_comm X Y i,
      range_map_of_isImmersion_of_comm (openScheme X T) (openScheme Y A) jOver]
    change _ = (Point.underlying : ComplexPoint (openScheme X T) →
      (openScheme X T).left) ⁻¹' Set.range j
    rw [range_closedImmersionSourceOpenLift i.left A]
    rfl
  have he : f (Point.map jOver z) = Point.map (openInclusion Y A ≫ i) z := by
    change Point.map (openInclusion X T) (Point.map jOver z) = _
    rw [← Point.map_comp_apply]
    exact congrArg (fun k ↦ Point.map k z)
      (Over.OverMorphism.ext (closedImmersionSourceOpenLift_ι i.left A))
  obtain ⟨W, hWV, hzW, hW⟩ := exists_smoothClosedSupportImageNeighborhood
    (openScheme X T) (openScheme Y A) jOver m d f
    (isOpenEmbedding_map_open X T) (Set.range (Point.map i)) hS z V (he ▸ hzV)
  exact ⟨W, hWV, he ▸ hzW, hW⟩

omit [SmoothOfRelativeDimension m Y.hom] in
/-- The fixed-dimensional source-open calculation, transported through a further actual
open embedding. This is the form used by successive closed supports in a larger ambient. -/
theorem exists_smoothClosedSourceOpenImageNeighborhood
    {M : Type} [TopologicalSpace M]
    (f : ComplexPoint X → M) (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (A : Y.left.Opens) [SmoothOfRelativeDimension m (openScheme Y A).hom]
    (z : ComplexPoint (openScheme Y A))
    (V : Opens M)
    (hzV : f (Point.map (openInclusion Y A ≫ i) z) ∈ V) :
    ∃ W : Opens M, W ≤ V ∧
      f (Point.map (openInclusion Y A ≫ i) z) ∈ W ∧
      ∀ n : ℕ, n ≠ 2 * (d - m) →
        IsZero (ModuleCat.of ℚ (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (W : Set M) S) n)) := by
  let V' : Opens (ComplexPoint X) := ⟨f ⁻¹' V, V.isOpen.preimage hf.continuous⟩
  obtain ⟨W', hW'V', hzW', hW'⟩ := exists_smoothClosedSourceOpenNeighborhood
    X Y i m d A z V' hzV
  let W : Opens M := ⟨f '' (W' : Set (ComplexPoint X)), hf.isOpenMap _ W'.isOpen⟩
  refine ⟨W, ?_, ⟨_, hzW', rfl⟩, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hW'V' hw
  · intro n hn
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W' : Set (ComplexPoint X))
          (Set.range (Point.map i))) n) := ModuleCat.subsingleton_of_isZero (hW' n hn)
    let e := neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W'
      (Set.range (Point.map i)) S (fun w _ => by rw [← hS]; rfl) n
    let : Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set M) S) n) := e.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _

end AlgebraicGeometry.ComplexPoint
