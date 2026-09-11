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

public import FormalConjecturesForMathlib.AlgebraicTopology.CenteredComplexEmbeddingOrientation

/-!
# A simultaneously normalized orientation class in a complex chart

The fixed complex-coordinate neighborhood cycle is transported through the actual compressed
inverse chart. Its point restrictions agree with `localClassOfChart` throughout the resulting
open neighborhood. Point excision in the chart target compares the two radial compressions;
the moving-center homotopy supplies their exact, not merely nonzero, normalization.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable (d : ℕ)

/-- A radial compression, with arbitrary source center, factored through an open target. -/
def radialTargetPointPairMap (U : Set (Fin d → ℂ)) (c : Fin d → ℂ) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball c r ⊆ U) (v q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q) :
    standardComplexPuncturedPair d ⟶ neighborhoodPointComplementPair U q := by
  have hmem (w : Fin d → ℂ) : OpenPartialHomeomorph.univBall c r (w + v) ∈ U := by
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target c hr]
    exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
  have hne (w : ({0}ᶜ : Set (Fin d → ℂ))) :
      OpenPartialHomeomorph.univBall c r (w.1 + v) ≠ q := by
    intro h
    exact w.2 (add_right_cancel (show w.1 + v = 0 + v by
      simpa using injective_complexUnivBall d c r (h.trans hq.symm)))
  refine TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨OpenPartialHomeomorph.univBall c r (w + v), hmem w⟩,
      by fun_prop⟩) ?_ ?_
  · refine TopCat.ofHom ⟨fun w => ⟨⟨OpenPartialHomeomorph.univBall c r (w.1 + v),
        hmem w.1⟩, hne w⟩, ?_⟩
    fun_prop
  · rfl

/-- Forgetting the target restriction displays exactly the centered radial map followed by
translation to its image point. -/
lemma radialTargetPointPairMap_comp_inclusion
    (U : Set (Fin d → ℂ)) (c : Fin d → ℂ) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball c r ⊆ U) (v q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q) :
    radialTargetPointPairMap d U c r hr hball v q hq ≫
      neighborhoodPointComplementPairMap U q =
      centeredComplexEmbeddingPair d (OpenPartialHomeomorph.univBall c r)
        (continuous_complexUnivBall d c r) (injective_complexUnivBall d c r) v ≫
          translationPointComplementPairMap (Fin d → ℂ) q := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    change OpenPartialHomeomorph.univBall c r (w.1 + v) =
      OpenPartialHomeomorph.univBall c r (w.1 + v) -
        OpenPartialHomeomorph.univBall c r v + q
    rw [hq, sub_add_cancel]
  · ext w
    have h (z : Fin d → ℂ) : OpenPartialHomeomorph.univBall c r (z + v) =
        OpenPartialHomeomorph.univBall c r (z + v) -
          OpenPartialHomeomorph.univBall c r v + q := by
      rw [hq, sub_add_cancel]
    exact h w

/-- The radial target class has the exact translated standard normalization. -/
lemma radialTargetPointPairMap_normalization
    (U : Set (Fin d → ℂ)) (c : Fin d → ℂ) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball c r ⊆ U) (v q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q) :
    relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap U q)
      (relativeHomologyMap ℚ (2 * d)
        (radialTargetPointPairMap d U c r hr hball v q hq) (standardComplexLocalClass d)) =
      relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) q)
        (standardComplexLocalClass d) := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    radialTargetPointPairMap_comp_inclusion, relativeHomologyMap_comp, LinearMap.comp_apply,
    centeredComplexUnivBall_preserves_standardComplexLocalClass d c r hr v]

/-- Two radial parameterizations with the same image point give identical classes inside
the open coordinate target. The proof uses genuine point excision. -/
theorem radialTargetPointPairMap_class_eq
    (U : Set (Fin d → ℂ)) (hU : IsOpen U)
    (c c' : Fin d → ℂ) (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r')
    (hball : Metric.ball c r ⊆ U) (hball' : Metric.ball c' r' ⊆ U)
    (v v' q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q)
    (hq' : OpenPartialHomeomorph.univBall c' r' v' = q) :
    relativeHomologyMap ℚ (2 * d)
      (radialTargetPointPairMap d U c r hr hball v q hq) (standardComplexLocalClass d) =
      relativeHomologyMap ℚ (2 * d)
        (radialTargetPointPairMap d U c' r' hr' hball' v' q hq')
          (standardComplexLocalClass d) := by
  have hqU : q ∈ U := by
    rw [← hq]
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target c hr]
    exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
  apply (neighborhoodPointComplement_relativeHomologyMap_bijective U q hU hqU (2 * d)).1
  rw [radialTargetPointPairMap_normalization, radialTargetPointPairMap_normalization]

variable {M : Type} [TopologicalSpace M]

/-- Apply the inverse chart on its genuine open target, with the distinguished point removed. -/
def chartTargetInversePointPairMap (e : OpenPartialHomeomorph M (Fin d → ℂ))
    (q : Fin d → ℂ) (hq : q ∈ e.target) :
    neighborhoodPointComplementPair e.target q ⟶ pointComplementPair (e.symm q) := by
  have hne (w : {w : e.target | w.1 ≠ q}) : e.symm w.1.1 ≠ e.symm q := fun h ↦
    w.2 (e.symm.injOn w.1.2 hq h)
  refine TopPair.ofHom
    (TopCat.ofHom ⟨fun w => e.symm w.1, e.symm.continuousOn.domRestrict⟩) ?_ ?_
  · exact TopCat.ofHom ⟨fun w => ⟨e.symm w.1.1, hne w⟩,
      (e.symm.continuousOn.domRestrict.comp continuous_subtype_val).subtype_mk hne⟩
  · rfl

variable (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

/-- The global continuous map supplied by the compressed inverse chart. -/
def chartOrientationEmbeddingMap : TopCat.of (Fin d → ℂ) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨chartModelEmbedding d e x hx,
    ((chartModelEmbedding d e x hx).isOpenEmbedding
      (chartModelEmbedding_source d e x hx)).continuous⟩

lemma chartOrientationEmbeddingMap_injective :
    Function.Injective (chartOrientationEmbeddingMap d e x hx) :=
  chartModelEmbedding_injective d e x hx

lemma chartOrientationEmbeddingMap_mem_source (v : Fin d → ℂ) :
    chartOrientationEmbeddingMap d e x hx v ∈ e.source := by
  apply e.symm.map_source
  apply ball_chartRadius_subset d e x hx
  rw [← OpenPartialHomeomorph.univBall_target (e x) (chartRadius_pos d e x hx)]
  exact (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).map_source (by simp)

lemma chartOrientationEmbeddingMap_coordinates (v : Fin d → ℂ) :
    e (chartOrientationEmbeddingMap d e x hx v) =
      OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) v := by
  apply e.right_inv
  apply ball_chartRadius_subset d e x hx
  rw [← OpenPartialHomeomorph.univBall_target (e x) (chartRadius_pos d e x hx)]
  exact (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).map_source (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- Translating in the compressed chart model and then transporting gives precisely the
existing chart-local orientation at the image point. -/
theorem chartOrientationEmbeddingMap_translate_standardComplexLocalClass (v : Fin d → ℂ) :
    relativeHomologyMap ℚ (2 * d)
      (translationPointComplementPairMap (Fin d → ℂ) v ≫
        imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
          (chartOrientationEmbeddingMap_injective d e x hx) v)
      (standardComplexLocalClass d) =
      localClassOfChart d e (chartOrientationEmbeddingMap d e x hx v)
        (chartOrientationEmbeddingMap_mem_source d e x hx v) := by
  let q := OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) v
  have hq : q ∈ e.target := by
    apply ball_chartRadius_subset d e x hx
    rw [← OpenPartialHomeomorph.univBall_target (e x) (chartRadius_pos d e x hx)]
    exact (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).map_source (by simp)
  let y := chartOrientationEmbeddingMap d e x hx v
  have hy : y ∈ e.source := chartOrientationEmbeddingMap_mem_source d e x hx v
  have hq' : OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) 0 = q := by
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    exact chartOrientationEmbeddingMap_coordinates d e x hx v
  let P := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) v q rfl
  let Q := radialTargetPointPairMap d e.target (e y) (chartRadius d e y hy)
    (chartRadius_pos d e y hy) (ball_chartRadius_subset d e y hy) 0 q hq'
  let I := chartTargetInversePointPairMap d e q hq
  have hP : translationPointComplementPairMap (Fin d → ℂ) v ≫
      imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
        (chartOrientationEmbeddingMap_injective d e x hx) v = P ≫ I := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w; apply Subtype.ext; rfl
    · ext w; rfl
  have hQ : chartModelEmbeddingPair d e y hy = Q ≫ I := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      change e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) w.1) =
        e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) (w.1 + 0))
      rw [add_zero]
    · ext w
      have h (z : Fin d → ℂ) :
          e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) z) =
            e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) (z + 0)) := by
        rw [add_zero]
      exact h w
  have hclasses : relativeHomologyMap ℚ (2 * d) P (standardComplexLocalClass d) =
      relativeHomologyMap ℚ (2 * d) Q (standardComplexLocalClass d) :=
    radialTargetPointPairMap_class_eq d e.target e.open_target
      (e x) (e y) (chartRadius d e x hx) (chartRadius d e y hy)
      (chartRadius_pos d e x hx) (chartRadius_pos d e y hy)
      (ball_chartRadius_subset d e x hx) (ball_chartRadius_subset d e y hy) v 0 q rfl hq'
  change relativeHomologyMap ℚ (2 * d) _ (standardComplexLocalClass d) =
    relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e y hy)
      (standardComplexLocalClass d)
  rw [hP, hQ, relativeHomologyMap_comp, relativeHomologyMap_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, hclasses]

/-- The image of the explicit coordinate orientation neighborhood in the given chart. -/
def chartOrientationNeighborhood : TopologicalSpace.Opens M :=
  ⟨chartOrientationEmbeddingMap d e x hx '' (standardComplexOrientationNeighborhood d : Set _),
    ((chartModelEmbedding d e x hx).isOpenEmbedding (chartModelEmbedding_source d e x hx)).isOpenMap
      _ (standardComplexOrientationNeighborhood d).isOpen⟩

lemma mem_chartOrientationNeighborhood : x ∈ chartOrientationNeighborhood d e x hx := by
  exact ⟨0, zero_mem_standardComplexOrientationNeighborhood d,
    chartModelEmbedding_zero d e x hx⟩

lemma chartOrientationNeighborhood_subset_source :
    (chartOrientationNeighborhood d e x hx : Set M) ⊆ e.source := by
  rintro y ⟨v, _, rfl⟩
  exact chartOrientationEmbeddingMap_mem_source d e x hx v

/-- The actual relative homology class on a chart neighborhood, constructed from the fixed
affine-simplex cycle. -/
def chartOrientationNeighborhoodClass :
    RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of M) (chartOrientationNeighborhood d e x hx : Set M)ᶜ)
      (2 * d) :=
  relativeHomologyMap ℚ (2 * d)
    (imageSupportPairMap (chartOrientationEmbeddingMap d e x hx)
      (chartOrientationEmbeddingMap_injective d e x hx) (standardComplexOrientationNeighborhood d))
    (standardComplexOrientationNeighborhoodClass d)

/-- One neighborhood-relative class simultaneously represents the exact existing chart-local
class at every point of its support. -/
theorem chartOrientationNeighborhoodClass_restrict (y : M)
    (hy : y ∈ chartOrientationNeighborhood d e x hx) :
    relativeHomologyMap ℚ (2 * d)
      (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy))
      (chartOrientationNeighborhoodClass d e x hx) =
      localClassOfChart d e y (chartOrientationNeighborhood_subset_source d e x hx hy) := by
  obtain ⟨v, hv, rfl⟩ := hy
  have hmap := congrArg (fun f => relativeHomologyMap ℚ (2 * d) f
      (standardComplexOrientationNeighborhoodClass d))
    (imageSupportPairMap_restrict (chartOrientationEmbeddingMap d e x hx)
      (chartOrientationEmbeddingMap_injective d e x hx)
      (standardComplexOrientationNeighborhood d) v hv)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, standardComplexOrientationNeighborhoodClass_restrict d v hv] at hmap
  calc
    _ = relativeHomologyMap ℚ (2 * d)
        (imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
          (chartOrientationEmbeddingMap_injective d e x hx) v)
        (relativeHomologyMap ℚ (2 * d) (translationPointComplementPairMap (Fin d → ℂ) v)
          (standardComplexLocalClass d)) := hmap
    _ = _ := by
      rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
      exact chartOrientationEmbeddingMap_translate_standardComplexLocalClass d e x hx v

end AlgebraicTopology.Singular
