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

public import FormalConjecturesForMathlib.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import FormalConjecturesForMathlib.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import FormalConjecturesForMathlib.AlgebraicTopology.NormalProjectionOverlap

/-!
# Exactly normalized smooth-support coclasses on actual overlaps

The previously constructed local normal coclass is the pullback of the fixed complex
normal coclass along the actual normal coordinate projection. The actual holomorphic
closed-immersion charts prove that these coclasses agree on sufficiently small common
ambient neighborhoods. No transition compatibility or purity equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- Actual normal-projection coclass on any subset of a holomorphic flattening chart. -/
def smoothClosedSupportChartCoclass (W : Set (ComplexPoint X))
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W (Set.range (Point.map i)))
      (2 * (d - m)) :=
  chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) W hW

/-- Restriction is the map induced by the actual inclusion of support-complement pairs. -/
theorem smoothClosedSupportChartCoclass_restrict
    {W V : Set (ComplexPoint X)} (hWV : W ⊆ V)
    (hV : V ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i)))
      (smoothClosedSupportChartCoclass X Y i m d z V hV) =
    smoothClosedSupportChartCoclass X Y i m d z W (hWV.trans hV) :=
  chartNormalProjectionCoclass_restrict _ _ _ _ _ hWV hV

/-- The old local pair-model coclass is exactly the actual chart-projection coclass.
The proof uses the explicit radial normal fiber, including its complex normalization. -/
theorem smoothClosedSupportNormalCoclass_eq_projection
    (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V) :
    smoothClosedSupportNormalCoclass X Y i m d z V hzV =
    chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
      (smoothClosedSupportRestrictionChart X Y i m d z V)
      (Set.range (Point.map i))
      (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
      (smoothClosedSupportNeighborhood X Y i m d z V hzV)
      (flattenedSupportNeighborhood_subset_source _ _ _ _ _) := by
  apply chartNormalProjectionCoclass_unique
    (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Set.range (Point.map i))
    (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    (Point.map i z)
    (smoothClosedSupportRestrictionChart_mem_source X Y i m d z V hzV)
    (congrArg Prod.snd (smoothClosedSupportRestrictionChart_center X Y i m d z V))
  exact smoothClosedSupportNormalCoclass_apply_class X Y i m d z V hzV

/-- On a common smaller neighborhood, restriction of the old local coclass is exactly
the holomorphic-chart coclass. Both maps are the same literal normal projection. -/
theorem smoothClosedSupportNormalCoclass_restrict_eq_chart
    (V : Opens (ComplexPoint X)) (hzV : Point.map i z ∈ V)
    (W : Set (ComplexPoint X))
    (hWV : W ⊆ smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i)))
      (smoothClosedSupportNormalCoclass X Y i m d z V hzV) =
    smoothClosedSupportChartCoclass X Y i m d z W hW := by
  rw [smoothClosedSupportNormalCoclass_eq_projection]
  exact chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart X Y i m d z V)
    (Set.range (Point.map i))
    (smoothClosedSupportRestrictionChart_mem_range_iff X Y i m d z V)
    hWV (flattenedSupportNeighborhood_subset_source _ _ _ _ _)

variable (z' : ComplexPoint Y)

/-- Exactly normalized ambient coclass agreement for the actual closed-immersion charts.
The only inputs are smoothness, the closed immersion, and membership in its actual chart
overlap and image. Holomorphicity and invertibility of the normal derivative are proved. -/
theorem exists_open_smoothClosedSupportChartCoclass_eq
    (x : ComplexPoint X) (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source) :
    ∃ (W : Opens (ComplexPoint X))
      (hW : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
      (hW' : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source),
      x ∈ W ∧ smoothClosedSupportChartCoclass X Y i m d z W hW =
        smoothClosedSupportChartCoclass X Y i m d z' W hW' := by
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e' := closedImmersionHolomorphicFlatteningChart X Y i m d z'
  have ht : e x ∈ (closedImmersionNormalTransition X Y i m d z z').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rwa [e.left_inv hx]
  exact exists_open_chartNormalProjectionCoclass_eq (d - m) e e' (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z')
    x hx ((closedImmersionHolomorphicFlatteningChart_mem_range_iff
      X Y i m d z x hx).mp hxS) hx'
    (analyticAt_closedImmersionNormalTransition X Y i m d z z' (e x) ht)
    (analyticAt_closedImmersionNormalTransition_symm X Y i m d z z' (e x) ht)

/-- Ambient overlap agreement remains cofinal inside any prescribed common open. -/
theorem exists_open_smoothClosedSupportChartCoclass_eq_within
    (x : ComplexPoint X) (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source)
    (U : Opens (ComplexPoint X)) (hxU : x ∈ U) :
    ∃ (W : Opens (ComplexPoint X))
      (hW : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
      (hW' : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source),
      x ∈ W ∧ W ≤ U ∧
      smoothClosedSupportChartCoclass X Y i m d z W hW =
        smoothClosedSupportChartCoclass X Y i m d z' W hW' := by
  obtain ⟨W₀, hW₀, hW₀', hxW₀, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq
    X Y i m d z z' x hxS hx hx'
  let W := W₀ ⊓ U
  have hWW₀ : (W : Set (ComplexPoint X)) ⊆ (W₀ : Set (ComplexPoint X)) :=
    fun _ hy => hy.1
  refine ⟨W, hWW₀.trans hW₀, hWW₀.trans hW₀', ⟨hxW₀, hxU⟩, inf_le_right, ?_⟩
  have h := congrArg (relativeCohomologyMap ℚ (2 * (d - m))
    (neighborhoodSupportInclusionPairMap hWW₀ (Set.range (Point.map i)))) heq
  simpa only [smoothClosedSupportChartCoclass_restrict] using h

/-- The original exactly normalized local normal coclasses agree after actual pair
restriction on sufficiently small ambient overlaps of the holomorphic chart loci.
This is a comparison theorem for the old classes, not a new definition of their duality. -/
theorem exists_open_smoothClosedSupportNormalCoclass_restrict_eq
    (V V' : Opens (ComplexPoint X))
    (hzV : Point.map i z ∈ V) (hzV' : Point.map i z' ∈ V')
    (x : ComplexPoint X) (hxS : x ∈ Set.range (Point.map i))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart X Y i m d z').source)
    (hxV : x ∈ smoothClosedSupportNeighborhood X Y i m d z V hzV)
    (hxV' : x ∈ smoothClosedSupportNeighborhood X Y i m d z' V' hzV') :
    ∃ (W : Opens (ComplexPoint X))
      (hWV : (W : Set (ComplexPoint X)) ⊆
        (smoothClosedSupportNeighborhood X Y i m d z V hzV : Set (ComplexPoint X)))
      (hWV' : (W : Set (ComplexPoint X)) ⊆
        (smoothClosedSupportNeighborhood X Y i m d z' V' hzV' : Set (ComplexPoint X))),
      x ∈ W ∧
      relativeCohomologyMap ℚ (2 * (d - m))
        (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i)))
        (smoothClosedSupportNormalCoclass X Y i m d z V hzV) =
      relativeCohomologyMap ℚ (2 * (d - m))
        (neighborhoodSupportInclusionPairMap hWV' (Set.range (Point.map i)))
        (smoothClosedSupportNormalCoclass X Y i m d z' V' hzV') := by
  obtain ⟨W, hW, hW', hxW, hWU, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq_within
    X Y i m d z z' x hxS hx hx'
    (smoothClosedSupportNeighborhood X Y i m d z V hzV ⊓
      smoothClosedSupportNeighborhood X Y i m d z' V' hzV') ⟨hxV, hxV'⟩
  have hWV : (W : Set (ComplexPoint X)) ⊆
      (smoothClosedSupportNeighborhood X Y i m d z V hzV : Set (ComplexPoint X)) :=
    fun _ hy => (hWU hy).1
  have hWV' : (W : Set (ComplexPoint X)) ⊆
      (smoothClosedSupportNeighborhood X Y i m d z' V' hzV' : Set (ComplexPoint X)) :=
    fun _ hy => (hWU hy).2
  refine ⟨W, hWV, hWV', hxW, ?_⟩
  rwa [smoothClosedSupportNormalCoclass_restrict_eq_chart X Y i m d z V hzV W hWV hW,
    smoothClosedSupportNormalCoclass_restrict_eq_chart X Y i m d z' V' hzV' W hWV' hW']

end AlgebraicGeometry.ComplexPoint
