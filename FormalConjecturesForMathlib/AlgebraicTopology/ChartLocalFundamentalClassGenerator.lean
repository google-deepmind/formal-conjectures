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

public import FormalConjecturesForMathlib.AlgebraicTopology.RelativePairExcision

import FormalConjecturesForMathlib.AlgebraicTopology.LocalFundamentalClassGenerator
import FormalConjecturesForMathlib.AlgebraicTopology.PuncturedEuclideanFundamentalClass

/-!
# Generator properties of chart-local fundamental classes

A compressed complex chart is a homeomorphism from `ℂ^d` onto its open target.  On relative
homology, its map to the ambient point-complement pair factors as the isomorphism onto that target
followed by open-neighborhood excision.  Consequently the chart map is an isomorphism and the
transported standard complex local class generates the full ambient local homology group.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
variable (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
  (hx : x ∈ e.source)

/-- The image of the compressed inverse chart, regarded as an open neighborhood of `x`. -/
abbrev chartModelTarget : Set M :=
  (chartModelEmbedding d e x hx).target

lemma chartModelEmbedding_range_eq_target :
    Set.range (chartModelEmbedding d e x hx) = chartModelTarget d e x hx := by
  rw [← Set.image_univ, ← chartModelEmbedding_source d e x hx]
  exact (chartModelEmbedding d e x hx).image_source_eq_target

lemma chartModelTarget_isOpen : IsOpen (chartModelTarget d e x hx) :=
  (chartModelEmbedding d e x hx).open_target

lemma chartModelTarget_mem : x ∈ chartModelTarget d e x hx := by
  have hzero : chartModelEmbedding d e x hx 0 ∈ chartModelTarget d e x hx :=
    (chartModelEmbedding d e x hx).map_source
      (by rw [chartModelEmbedding_source]; trivial)
  simpa only [chartModelEmbedding_zero] using hzero

/-- The compressed inverse chart as a homeomorphism onto its open target. -/
def chartModelTargetHomeomorph :
    (Fin d → ℂ) ≃ₜ chartModelTarget d e x hx :=
  ((chartModelEmbedding d e x hx).isOpenEmbedding
      (chartModelEmbedding_source d e x hx)).isEmbedding.toHomeomorph |>.trans
    (Homeomorph.setCongr (chartModelEmbedding_range_eq_target d e x hx))

@[simp]
lemma chartModelTargetHomeomorph_apply_val (y : Fin d → ℂ) :
    (chartModelTargetHomeomorph d e x hx y).1 = chartModelEmbedding d e x hx y :=
  rfl

/-- The target homeomorphism restricted away from the distinguished points. -/
def puncturedChartModelTargetHomeomorph :
    ({0}ᶜ : Set (Fin d → ℂ)) ≃ₜ
      {y : chartModelTarget d e x hx | y.1 ≠ x} :=
  (chartModelTargetHomeomorph d e x hx).subtype fun y ↦ by
    change y ≠ 0 ↔ chartModelEmbedding d e x hx y ≠ x
    refine not_congr ⟨fun hzero ↦ ?_, fun hxy ↦ chartModelEmbedding_injective d e x hx ?_⟩
    · rw [hzero, chartModelEmbedding_zero d e x hx]
    · rw [chartModelEmbedding_zero d e x hx]
      exact hxy

/-- The pair isomorphism from the standard complex local model to the open chart target. -/
def standardComplexChartTargetPairIso :
    standardComplexPuncturedPair d ≅
      neighborhoodPointComplementPair (chartModelTarget d e x hx) x where
  hom := TopPair.ofHom
    (TopCat.ofHom ⟨chartModelTargetHomeomorph d e x hx,
      (chartModelTargetHomeomorph d e x hx).continuous⟩)
    (TopCat.ofHom ⟨puncturedChartModelTargetHomeomorph d e x hx,
      (puncturedChartModelTargetHomeomorph d e x hx).continuous⟩)
    (by ext y; rfl)
  inv := TopPair.ofHom
    (TopCat.ofHom ⟨(chartModelTargetHomeomorph d e x hx).symm,
      (chartModelTargetHomeomorph d e x hx).symm.continuous⟩)
    (TopCat.ofHom ⟨(puncturedChartModelTargetHomeomorph d e x hx).symm,
      (puncturedChartModelTargetHomeomorph d e x hx).symm.continuous⟩)
    (by ext y; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      exact (puncturedChartModelTargetHomeomorph d e x hx).left_inv y
    · ext y
      exact (chartModelTargetHomeomorph d e x hx).left_inv y
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      exact (puncturedChartModelTargetHomeomorph d e x hx).right_inv y
    · ext y
      exact (chartModelTargetHomeomorph d e x hx).right_inv y

/-- The original chart map factors through its open target and the neighborhood inclusion. -/
lemma standardComplexChartTargetPairIso_hom_comp_neighborhoodMap :
    (standardComplexChartTargetPairIso d e x hx).hom ≫
        neighborhoodPointComplementPairMap (chartModelTarget d e x hx) x =
      chartModelEmbeddingPair d e x hx := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext y
    apply Subtype.ext
    rfl
  · ext y
    exact chartModelTargetHomeomorph_apply_val d e x hx y

variable [T1Space M]

/-- The compressed chart induces a bijection from standard complex local homology to ambient
local homology. -/
theorem chartModelEmbedding_relativeHomologyMap_bijective :
    Function.Bijective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) := by
  have htarget : Function.Bijective
      (relativeHomologyMap ℚ (2 * d)
        (standardComplexChartTargetPairIso d e x hx).hom) := by
    exact (ConcreteCategory.isIso_iff_bijective ((relativeHomologyFunctor ℚ (2 * d)).map
      (standardComplexChartTargetPairIso d e x hx).hom)).mp inferInstance
  have hexcision := neighborhoodPointComplement_relativeHomologyMap_bijective
    (chartModelTarget d e x hx) x (chartModelTarget_isOpen d e x hx)
      (chartModelTarget_mem d e x hx) (2 * d)
  rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d e x hx,
    relativeHomologyMap_comp]
  exact hexcision.comp htarget

/-- The compressed chart is surjective on local homology. -/
theorem chartModelEmbedding_relativeHomologyMap_surjective :
    Function.Surjective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) :=
  (chartModelEmbedding_relativeHomologyMap_bijective d e x hx).2

omit [T1Space M] in
/-- The oriented standard complex class generates its local homology in every complex
dimension. -/
lemma span_standardComplexLocalClass_eq_top_for_chart :
    Submodule.span ℚ {standardComplexLocalClass d} = ⊤ := by
  cases d with
  | zero => exact span_standardComplexLocalClass_zero_eq_top
  | succ n =>
      rw [span_standardComplexLocalClass_eq_top_iff]
      have hdeg : (n + 1) * 2 = n * 2 + 2 := by lia
      rw [hdeg]
      exact span_standardLocalClass_add_two_eq_top (n * 2)

/-- The oriented standard complex local class is nonzero in every complex dimension. -/
lemma standardComplexLocalClass_ne_zero_for_chart :
    standardComplexLocalClass d ≠ 0 := by
  rw [standardComplexLocalClass_ne_zero_iff]
  by_cases hd : d = 0
  · subst d
    exact standardLocalClass_zero_ne_zero
  · exact standardLocalClass_ne_zero_of_pos (d * 2)
      (Nat.mul_pos (Nat.pos_of_ne_zero hd) (by norm_num))

/-- The class transported through a complex chart generates the full ambient rational local
homology group. -/
theorem span_localClassOfChart_eq_top :
    Submodule.span ℚ {localClassOfChart d e x hx} = ⊤ := by
  let f := relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)
  calc
    Submodule.span ℚ {localClassOfChart d e x hx} =
        (Submodule.span ℚ {standardComplexLocalClass d}).map f := by
      rw [Submodule.map_span]
      simp only [Set.image_singleton]
      rfl
    _ = (⊤ : Submodule ℚ _).map f := by
      rw [span_standardComplexLocalClass_eq_top_for_chart]
    _ = LinearMap.range f := Submodule.map_top f
    _ = ⊤ := LinearMap.range_eq_top.mpr
      (chartModelEmbedding_relativeHomologyMap_surjective d e x hx)

/-- The exactly normalized local class transported through a chart is nonzero. -/
theorem localClassOfChart_ne_zero :
    localClassOfChart d e x hx ≠ 0 := by
  have hinjective : Function.Injective
      (relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)) :=
    (chartModelEmbedding_relativeHomologyMap_bijective d e x hx).1
  intro hzero
  apply standardComplexLocalClass_ne_zero_for_chart d
  apply hinjective
  simpa only [localClassOfChart, hzero, map_zero]

end AlgebraicTopology.Singular
