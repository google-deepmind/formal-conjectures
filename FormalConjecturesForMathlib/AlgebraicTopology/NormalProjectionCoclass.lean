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

public import FormalConjecturesForMathlib.AlgebraicTopology.FlattenedSupportLocalHomology
public import FormalConjecturesForMathlib.AlgebraicTopology.CenteredComplexEmbeddingOrientation
public import FormalConjecturesForMathlib.AlgebraicGeometry.CycleComponentPurity

/-!
# Actual normal projections and the local support coclass

The normal projection of a support-flattening chart is a genuine map of pairs on every open
subset of its source. Pulling back the fixed normal coclass along this map is compatible with
restriction. The explicit radial-fiber factorization below identifies this coclass with the
previously constructed exactly normalized local coclass.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]

/-- Inclusion of actual neighborhood/support-complement pairs. -/
def neighborhoodSupportInclusionPairMap {W V : Set M} (hWV : W ⊆ V) (S : Set M) :
    neighborhoodSupportComplementPair W S ⟶ neighborhoodSupportComplementPair V S :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, continuous_subtype_val.subtype_mk _⟩)
    (TopCat.ofHom ⟨fun w => ⟨⟨w.1.1, hWV w.1.2⟩, w.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _⟩) (by ext w; rfl)

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)

/-- The actual normal projection from a neighborhood support pair. -/
def chartNormalProjectionPair (W : Set M) (hW : W ⊆ e.source) :
    neighborhoodSupportComplementPair W S ⟶ standardComplexPuncturedPair c :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun w => (e w.1).2, ((e.continuousOn.mono hW).domRestrict).snd⟩)
    (TopCat.ofHom ⟨fun w => ⟨(e w.1.1).2, fun h => w.2 ((hS _ (hW w.1.2)).mpr h)⟩,
      ((((e.continuousOn.mono hW).domRestrict).comp continuous_subtype_val).snd).subtype_mk _⟩)
    (by ext w; rfl)

omit [NormedSpace ℝ E] in
theorem neighborhoodSupportInclusion_comp_chartNormalProjection
    {W V : Set M} (hWV : W ⊆ V) (hV : V ⊆ e.source) :
    neighborhoodSupportInclusionPairMap hWV S ≫ chartNormalProjectionPair E c e S hS V hV =
      chartNormalProjectionPair E c e S hS W (hWV.trans hV) := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- The coclass on a whole chart neighborhood is the actual normal-projection pullback. -/
def chartNormalProjectionCoclass (W : Set M) (hW : W ⊆ e.source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W S) (2 * c) :=
  relativeCohomologyMap ℚ (2 * c) (chartNormalProjectionPair E c e S hS W hW)
    (normalizedDual (standardComplexLocalClass c) (standardComplexLocalClass_ne_zero_for_chart c))

omit [NormedSpace ℝ E] in
/-- The chart coclass is compatible with actual neighborhood inclusion. -/
theorem chartNormalProjectionCoclass_restrict {W V : Set M} (hWV : W ⊆ V) (hV : V ⊆ e.source) :
    relativeCohomologyMap ℚ (2 * c) (neighborhoodSupportInclusionPairMap hWV S)
      (chartNormalProjectionCoclass E c e S hS V hV) =
        chartNormalProjectionCoclass E c e S hS W (hWV.trans hV) := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    neighborhoodSupportInclusion_comp_chartNormalProjection]

/-- On a zero-tangent fiber, the product radial compression has exactly the usual
normal radial compression, including its scale. -/
theorem univBall_zero_tangent_normal (a : E) (r : ℝ) (hr : 0 < r) (v : Fin c → ℂ) :
    (OpenPartialHomeomorph.univBall (a, (0 : Fin c → ℂ)) r (0, v)).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) r v := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr, OpenPartialHomeomorph.univBall, dif_pos hr]
  change (r • ((Real.sqrt (1 + ‖((0 : E), v)‖ ^ 2))⁻¹ • ((0 : E), v)) + (a, 0)).2 =
    r • ((Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v) + 0
  simp

variable (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- The actual normal fiber, local pair homeomorphism, and normal projection compose
to the standard radial point-complement map, with no scalar ambiguity. -/
theorem normalFiber_comp_chartNormalProjection :
    normalSliceSection E c ≫ (flattenedSupportPairIso E c e x hx S hS h0).hom ≫
      chartNormalProjectionPair E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx) =
      centeredComplexEmbeddingPair c
        (OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx))
        (continuous_complexUnivBall c _ _) (injective_complexUnivBall c _ _) 0 := by
  have hp (v : Fin c → ℂ) :
      (e (flattenedSupportHomeomorph E c e x hx (0, v))).2 =
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx) v := by
    rw [flattenedSupportHomeomorph_coordinates]
    have he : e x = ((e x).1, (0 : Fin c → ℂ)) := Prod.ext rfl h0
    rw [he]
    exact univBall_zero_tangent_normal E c _ _ (flattenedSupportRadius_pos E c e x hx) v
  apply MorphismProperty.Arrow.Hom.ext
  · ext v
    apply Subtype.ext
    change (e (flattenedSupportHomeomorph E c e x hx (0, v.1))).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx) (v.1 + 0) -
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx) 0
    simpa only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero] using hp v.1
  · ext v
    change Fin c → ℂ at v
    change (e (flattenedSupportHomeomorph E c e x hx (0, v))).2 =
      OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx) (v + 0) -
        OpenPartialHomeomorph.univBall (0 : Fin c → ℂ) (flattenedSupportRadius E c e x hx) 0
    simpa only [add_zero, OpenPartialHomeomorph.univBall_apply_zero, sub_zero] using hp v

/-- The previously constructed class is exactly the image of the fixed class on this
actual normal fiber. -/
theorem flattenedSupportNormalClass_eq_normalFiber :
    flattenedSupportNormalClass E c e x hx S hS h0 =
      relativeHomologyMap ℚ (2 * c)
        (normalSliceSection E c ≫ (flattenedSupportPairIso E c e x hx S hS h0).hom)
        (standardComplexLocalClass c) := by
  rw [relativeHomologyMap_comp]
  rfl

/-- Normal projection sends the actual local normal class to the exact standard class. -/
theorem chartNormalProjection_normalClass :
    relativeHomologyMap ℚ (2 * c)
      (chartNormalProjectionPair E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx))
      (flattenedSupportNormalClass E c e x hx S hS h0) = standardComplexLocalClass c := by
  rw [flattenedSupportNormalClass_eq_normalFiber, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, Category.assoc, normalFiber_comp_chartNormalProjection]
  exact centeredComplexUnivBall_preserves_standardComplexLocalClass c _ _
    (flattenedSupportRadius_pos E c e x hx) 0

/-- The actual chart-projection coclass has precisely the required normalization. -/
theorem chartNormalProjectionCoclass_apply_normalClass :
    chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
      (flattenedSupportNeighborhood_subset_source E c e x hx)
      (flattenedSupportNormalClass E c e x hx S hS h0) = 1 := by
  change normalizedDual (standardComplexLocalClass c) (standardComplexLocalClass_ne_zero_for_chart c)
    (relativeHomologyMap ℚ (2 * c) _ (flattenedSupportNormalClass E c e x hx S hS h0)) = 1
  rw [chartNormalProjection_normalClass, normalizedDual_apply_self]

/-- Generation follows from the already constructed pair isomorphism and contraction. -/
theorem span_flattenedSupportNormalClass_eq_top :
    Submodule.span ℚ {flattenedSupportNormalClass E c e x hx S hS h0} = ⊤ := by
  let eH := (flattenedSupportRelativeHomologyIso E c e x hx S hS h0 (2 * c)).symm.toLinearEquiv
  have h := congrArg (Submodule.map eH.toLinearMap) (span_standardComplexLocalClass_eq_top_for_chart c)
  rwa [Submodule.map_span, Set.image_singleton, Submodule.map_top, LinearEquiv.range] at h

include h0 in
/-- In top normal degree the actual normal projection is injective; this is deduced from
the pair computation and its exact normalization, not used to construct the comparison. -/
theorem chartNormalProjection_relativeHomologyMap_injective :
    Function.Injective (relativeHomologyMap ℚ (2 * c)
      (chartNormalProjectionPair E c e S hS (flattenedSupportNeighborhood E c e x hx)
        (flattenedSupportNeighborhood_subset_source E c e x hx))) := by
  intro v w hvw
  have hg := (Submodule.span_singleton_eq_top_iff ℚ
    (flattenedSupportNormalClass E c e x hx S hS h0)).mp
    (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0)
  obtain ⟨r, rfl⟩ := hg v
  obtain ⟨s, rfl⟩ := hg w
  rw [map_smul, map_smul, chartNormalProjection_normalClass] at hvw
  rw [smul_left_injective ℚ (standardComplexLocalClass_ne_zero_for_chart c) hvw]

/-- A local supported coclass equals the actual normal-projection coclass precisely when
it evaluates to one on the constructed normal class. -/
theorem chartNormalProjectionCoclass_unique
    (α : RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (flattenedSupportNeighborhood E c e x hx) S) (2 * c))
    (hα : α (flattenedSupportNormalClass E c e x hx S hS h0) = 1) :
    α = chartNormalProjectionCoclass E c e S hS (flattenedSupportNeighborhood E c e x hx)
      (flattenedSupportNeighborhood_subset_source E c e x hx) := by
  have hne : flattenedSupportNormalClass E c e x hx S hS h0 ≠ 0 := by
    intro hz
    have h := chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0
    rw [hz, map_zero] at h
    exact zero_ne_one h
  exact (normalizedDual_unique hne (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0) α hα).trans
    (normalizedDual_unique hne (span_flattenedSupportNormalClass_eq_top E c e S hS x hx h0) _
      (chartNormalProjectionCoclass_apply_normalClass E c e S hS x hx h0)).symm

end AlgebraicTopology.Singular
