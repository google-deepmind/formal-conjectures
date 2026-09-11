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

public import FormalConjecturesForMathlib.AlgebraicGeometry.AnalyticDifferentialForms
public import FormalConjecturesForMathlib.Analysis.Calculus.DifferentialForm.HolomorphicPoincare
public import FormalConjecturesForMathlib.Analysis.NormedSpace.WedgeCovectors

import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The holomorphic Poincare operator on a complex-point space

This file applies the holomorphic Poincaré lemma of
`FormalConjecturesForMathlib.Analysis.Calculus.DifferentialForm.HolomorphicPoincare` to fixed-chart
evaluations of raw holomorphic forms on the analytic complex-point space of a complex scheme.
-/

@[expose] public noncomputable section

open ContinuousAlternatingMap MeasureTheory
open scoped ContDiff Interval

namespace AlgebraicGeometry.ComplexPoint

open Point

open CategoryTheory TopologicalSpace
open scoped Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Restricting a holomorphic function does not change its value in a fixed chart. -/
lemma chartSection_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d V z) :
    chartSection X d V z (holomorphicRestrictionAlgHom X d i f) y =
      chartSection X d U z f y := by
  have hyU : y ∈ chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  rw [chartSection_apply_of_mem X d V z _ hy,
    chartSection_apply_of_mem X d U z _ hyU]
  rfl

/-- Restricting a holomorphic function does not change its derivative in a fixed chart. -/
lemma chartSectionDifferential_holomorphicRestrictionAlgHom
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d V z) :
    chartSectionDifferential X d V z
        (holomorphicRestrictionAlgHom X d i f) y =
      chartSectionDifferential X d U z f y := by
  have hyU : y ∈ chartSectionDomain X d U z :=
    ⟨hy.1, leOfHom i.unop hy.2⟩
  have heq : Filter.EventuallyEq (nhds y)
      (chartSection X d V z
        (holomorphicRestrictionAlgHom X d i f))
      (chartSection X d U z f) := by
    filter_upwards [(isOpen_chartSectionDomain X d V z).mem_nhds hy] with w hw
    exact chartSection_holomorphicRestrictionAlgHom X d i z f hw
  rw [chartSectionDifferential, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V z) hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hyU]
  exact heq.fderiv_eq

/-- Fixed-chart evaluation of a differential form commutes with restriction. -/
lemma chartEvaluation_formRestriction
    [SmoothOfRelativeDimension d X.hom]
    {U V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ} (i : U ⟶ V)
    (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d V z) :
    chartEvaluation X d V z p (formRestriction X d i p θ) y =
      chartEvaluation X d U z p θ y := by
  have hyU : y ∈ chartSectionDomain X d U z := ⟨hy.1, leOfHom i.unop hy.2⟩
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      rw [formRestriction_mk, chartEvaluation_mk X d V z p _ _ hy,
        chartEvaluation_mk X d U z p a₀ v hyU]
      simp only [chartGeneratorEvaluation]
      rw [chartSection_holomorphicRestrictionAlgHom X d i z a₀ hy]
      have hd :
          (fun j ↦ chartSectionDifferential X d V z
            (holomorphicRestrictionAlgHom X d i (v j)) y) =
          (fun j ↦ chartSectionDifferential X d U z (v j) y) := by
        funext j
        exact chartSectionDifferential_holomorphicRestrictionAlgHom X d i z (v j) hy
      rw [hd]
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | smul c a ha => simp [ha]

/-- For the analytic charted-space instance, `chartAt` is the algebraically constructed local
chart. -/
lemma chartAt_eq_localChart [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    chartAt (Fin d → ℂ) z = localChart X d z := rfl

/-- The change of coordinates from the chart at `z'` to the chart at `z`. -/
def fixedChartTransition [SmoothOfRelativeDimension d X.hom]
    (z z' : ComplexPoint X) : (Fin d → ℂ) → (Fin d → ℂ) :=
  fun y ↦ (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y)

/-- A fixed-chart transition is complex analytic wherever the two charts overlap. -/
lemma analyticAt_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (z z' : ComplexPoint X) {y : Fin d → ℂ}
    (hy : y ∈ ((localChart X d z').symm.trans
      (localChart X d z)).source) :
    AnalyticAt ℂ (fixedChartTransition X d z z') y := by
  change AnalyticAt ℂ
    (fun v ↦ localChart X d z ((localChart X d z').symm v)) y
  exact analyticAt_localChart_transition X d z' z hy

/-- Expressions of a section in two overlapping fixed charts are related by the chart
transition. -/
lemma chartSection_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartSection X d U z' f y =
      chartSection X d U z f (fixedChartTransition X d z z' y) := by
  simp only [chartSection, Function.comp_apply, fixedChartTransition]
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hy]

/-- The coordinate derivatives of a section obey the chain rule under a fixed-chart
transition. -/
lemma chartSectionDifferential_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartSectionDifferential X d U z' f y =
      (chartSectionDifferential X d U z f
        (fixedChartTransition X d z z' y)).comp
          (fderiv ℂ (fixedChartTransition X d z z') y) := by
  have htransLocal : y ∈ ((localChart X d z').symm.trans
      (localChart X d z)).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · change y ∈ (localChart X d z').target
      simpa only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
        ModelWithCorners.range_eq_univ, Set.inter_univ,
        chartAt_eq_localChart X d] using hy.1
    · change (localChart X d z').symm y ∈
        (localChart X d z).source
      simpa only [extChartAt_coe_symm, extChartAt_source,
        modelWithCornersSelf_coe_symm, Function.comp_id,
        chartAt_eq_localChart X d] using hyz
  have hT : DifferentiableAt ℂ (fixedChartTransition X d z z') y :=
    (analyticAt_fixedChartTransition X d z z' htransLocal).differentiableAt
  have hTy : fixedChartTransition X d z z' y ∈
      chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [show fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hy.2
  have hf : DifferentiableAt ℂ (chartSection X d U z f)
      (fixedChartTransition X d z z' y) :=
    ((chartSection_contDiffWithinAt X d U z f hTy).contDiffAt
      ((isOpen_chartSectionDomain X d U z).mem_nhds hTy)).differentiableAt (by simp)
  have heq : Filter.EventuallyEq (nhds y)
      (chartSection X d U z' f)
      (chartSection X d U z f ∘ fixedChartTransition X d z z') := by
    filter_upwards [((localChart X d z').symm.trans
      (localChart X d z)).open_source.mem_nhds htransLocal] with w hw
    apply chartSection_fixedChartTransition X d U z z' f
    rw [OpenPartialHomeomorph.trans_source] at hw
    have hw2 := hw.2
    change (localChart X d z').symm w ∈
      (localChart X d z).source at hw2
    simpa only [extChartAt_coe_symm, extChartAt_source,
      modelWithCornersSelf_coe_symm, Function.comp_id,
      chartAt_eq_localChart X d] using hw2
  rw [chartSectionDifferential, chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z') hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hTy,
    heq.fderiv_eq]
  exact fderiv_fun_comp y hf hT

/-- Wedges of covectors commute with pullback along a continuous linear map. -/
lemma wedgeCovectors_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : ℕ) (L : Fin p → F →L[ℂ] ℂ) (T : E →L[ℂ] F) :
    wedgeCovectors E p (fun i ↦ (L i).comp T) =
      (wedgeCovectors F p L).compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [wedgeCovectors_apply_eq_det, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    wedgeCovectors_apply_eq_det]
  rfl

lemma add_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (a b : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (a + b).compContinuousLinearMap T =
      a.compContinuousLinearMap T + b.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma smul_compContinuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : ℕ} (c : ℂ) (a : F [⋀^Fin p]→L[ℂ] ℂ) (T : E →L[ℂ] F) :
    (c • a).compContinuousLinearMap T = c • a.compContinuousLinearMap T := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Evaluation of a differential form is covariant under a holomorphic fixed-chart
transition. -/
lemma chartEvaluation_fixedChartTransition
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z z' : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z')
    (hyz : (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source) :
    chartEvaluation X d U z' p θ y =
      (chartEvaluation X d U z p θ
        (fixedChartTransition X d z z' y)).compContinuousLinearMap
          (fderiv ℂ (fixedChartTransition X d z z') y) := by
  have hTy : fixedChartTransition X d z z' y ∈ chartSectionDomain X d U z := by
    refine ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).map_source hyz, ?_⟩
    change (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      (fixedChartTransition X d z z' y) ∈
        ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [show fixedChartTransition X d z z' y =
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
          ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y) from rfl,
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hyz]
    exact hy.2
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ v =>
      rw [chartEvaluation_mk X d U z' p a₀ v hy, chartEvaluation_mk X d U z p a₀ v hTy]
      simp only [chartGeneratorEvaluation]
      rw [chartSection_fixedChartTransition X d U z z' a₀ hyz]
      have hd :
          (fun j ↦ chartSectionDifferential X d U z' (v j) y) =
          (fun j ↦ (chartSectionDifferential X d U z (v j)
            (fixedChartTransition X d z z' y)).comp
              (fderiv ℂ (fixedChartTransition X d z z') y)) := by
        funext j
        exact chartSectionDifferential_fixedChartTransition X d U z z' (v j) hy hyz
      rw [hd, wedgeCovectors_compContinuousLinearMap, smul_compContinuousLinearMap]
  | zero =>
      rw [chartEvaluation_zero]
      exact ContinuousAlternatingMap.ext fun v ↦ by
        simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  | add a b ha hb =>
      simp only [chartEvaluation_add, Pi.add_apply, ha, hb, add_compContinuousLinearMap]
  | smul c a ha =>
      simp only [chartEvaluation_smul, Pi.smul_apply, ha, smul_compContinuousLinearMap]

/-- Vanishing throughout one fixed chart detects a restriction-stable analytic relation, provided
the open set lies in the source of that chart. -/
lemma mem_restrictionStableAnalyticKernel_of_chartEvaluation_eq_zero
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) :
      Set (ComplexPoint X)) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (hθ : Set.EqOn (chartEvaluation X d U z p θ) 0
      (chartSectionDomain X d U z)) :
    θ ∈ restrictionStableAnalyticKernel X d U p := by
  rw [restrictionStableAnalyticKernel]
  simp only [Submodule.mem_iInf, Submodule.mem_comap]
  intro V i
  apply (mem_chartEvaluationKernel_iff X d V p _).2
  intro z' y hy
  rw [chartEvaluation_formRestriction X d i z' p θ hy]
  have hyU :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
        ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) :=
    leOfHom i.unop hy.2
  have hyz :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z').symm y ∈
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source :=
    hsource hyU
  rw [chartEvaluation_fixedChartTransition X d U z z' p θ ⟨hy.1, hyU⟩ hyz]
  have hTy : fixedChartTransition X d z z' y ∈
      chartSectionDomain X d U z := by
    let ez := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z
    let ez' := extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z'
    refine ⟨ez.map_source hyz, ?_⟩
    change ez.symm (fixedChartTransition X d z z' y) ∈
      ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [show fixedChartTransition X d z z' y = ez (ez'.symm y) from rfl,
      ez.left_inv hyz]
    exact hyU
  rw [hθ hTy]
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

lemma contMDiffAt_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {q : ComplexPoint X} (hq : q ∈ Opposite.unop U) :
    ContMDiffAt (modelWithCornersSelf ℂ (Fin d → ℂ))
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x)) q := by
  have hqsource := hsource hq
  have hcoord :
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q ∈
        chartSectionDomain X d U z := by
    refine ⟨(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).map_source hqsource, ?_⟩
    change (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q) ∈
        ((Opposite.unop U : Opens (ComplexPoint X)) : Set _)
    rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).left_inv hqsource]
    exact hq
  exact (ha _ hcoord).contDiffAt.contMDiffAt.comp q
    (contMDiffAt_extChartAt' (by
      rwa [← extChartAt_source (modelWithCornersSelf ℂ (Fin d → ℂ))]))

lemma contMDiff_chartFunction [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z)) :
    ContMDiff (modelWithCornersSelf ℂ (Fin d → ℂ)) (modelWithCornersSelf ℂ ℂ) ω
      (fun q : (Opposite.unop U : Opens (ComplexPoint X)) ↦
        a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q)) :=
  fun q ↦ (contMDiffAt_subtype_iff
    (I := modelWithCornersSelf ℂ (Fin d → ℂ))
    (I' := modelWithCornersSelf ℂ ℂ)
    (U := (Opposite.unop U : Opens (ComplexPoint X)))
    (f := fun x : ComplexPoint X ↦
      a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) x))
    (x := q)).mpr (contMDiffAt_chartFunction X d U z hsource a ha q.2)

/-- An analytic scalar function in one chart, regarded as a holomorphic section on the chart
source. -/
def holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z)) :
    OpenHolomorphicFunctions X d U := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint X)); ℂ⟯
  exact ⟨fun q ↦ a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z) q),
    contMDiff_chartFunction X d U z hsource a ha⟩

lemma chartSection_holomorphicSectionOfChart [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z
        (holomorphicSectionOfChart X d U z hsource a ha) y = a y := by
  rw [chartSection_apply_of_mem X d U z _ hy]
  change a ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z)
    ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).symm y)) = a y
  rw [(extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).right_inv hy.1]

lemma chartSectionDifferential_holomorphicSectionOfChart
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (a : (Fin d → ℂ) → ℂ)
    (ha : AnalyticOnNhd ℂ a (chartSectionDomain X d U z))
    {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
        (holomorphicSectionOfChart X d U z hsource a ha) y =
      fderivWithin ℂ a (chartSectionDomain X d U z) y := by
  rw [chartSectionDifferential]
  exact fderivWithin_congr'
    (fun w hw ↦ chartSection_holomorphicSectionOfChart X d U z hsource a ha hw) hy

/-- The `i`-th fixed-chart coordinate as a holomorphic section. -/
def chartCoordinateSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) : OpenHolomorphicFunctions X d U :=
  holomorphicSectionOfChart X d U z hsource
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).analyticOnNhd _)

lemma chartSection_chartCoordinateSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSection X d U z (chartCoordinateSection X d U z hsource i) y =
      y i := by
  unfold chartCoordinateSection
  exact chartSection_holomorphicSectionOfChart X d U z hsource _ _ hy

lemma chartSectionDifferential_chartCoordinateSection
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (i : Fin d) {y : Fin d → ℂ} (hy : y ∈ chartSectionDomain X d U z) :
    chartSectionDifferential X d U z
        (chartCoordinateSection X d U z hsource i) y =
      ContinuousLinearMap.proj i := by
  unfold chartCoordinateSection
  rw [chartSectionDifferential_holomorphicSectionOfChart X d U z hsource _ _ hy,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hy]
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) i).hasFDerivAt.fderiv

/-- The product of a tuple of coordinate covectors. -/
def covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin p) ℂ).compContinuousLinearMap
    (fun j ↦ ContinuousLinearMap.proj (I j))

@[simp] lemma covectorProduct_apply (d p : ℕ) (I : Fin p → Fin d)
    (v : Fin p → Fin d → ℂ) :
    covectorProduct d p I v = ∏ j, v j (I j) := by
  simp [covectorProduct, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- A multilinear form on a finite product is the sum of its coordinate monomials. -/
lemma multilinear_eq_sum_covectorProduct (d p : ℕ)
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    A = ∑ I : Fin p → Fin d,
      A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  change A.toMultilinearMap =
    ContinuousMultilinearMap.toMultilinearMapLinear
      (R' := ℂ) (∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) • covectorProduct d p I)
  rw [_root_.map_sum]
  simp_rw [_root_.map_smul]
  refine Module.Basis.ext_multilinear (fun _ : Fin p ↦ Pi.basisFun ℂ (Fin d)) fun v ↦ ?_
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single v]
  · simp [Pi.basisFun_apply]
  · intro I hI hne
    change A (fun j ↦ Pi.single (I j) 1) *
      covectorProduct d p I (fun j ↦ Pi.basisFun ℂ (Fin d) (v j)) = 0
    rw [covectorProduct_apply]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hz : (Pi.basisFun ℂ (Fin d) (v j)) (I j) = 0 := by
      simp [Pi.basisFun_apply, hj.symm]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
  · simp

/-- Alternatizing a coordinate monomial gives the wedge of its coordinate covectors. -/
lemma alternatization_covectorProduct (d p : ℕ) (I : Fin p → Fin d) :
    ContinuousMultilinearMap.alternatization (covectorProduct d p I) =
      wedgeCovectors (Fin d → ℂ) p (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeCovectors_apply_eq_det, ← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [covectorProduct_apply]
  congr 1

lemma alternatization_smul (d p : ℕ) (c : ℂ)
    (M : ContinuousMultilinearMap ℂ (fun _ : Fin p ↦ Fin d → ℂ) ℂ) :
    ContinuousMultilinearMap.alternatization (c • M) =
      c • ContinuousMultilinearMap.alternatization M := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [ContinuousMultilinearMap.alternatization_apply_apply, _root_.smul_apply,
    ContinuousAlternatingMap.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [smul_comm]

lemma alternatization_toContinuousMultilinearMap (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    ContinuousMultilinearMap.alternatization A.toContinuousMultilinearMap =
      (p.factorial : ℂ) • A := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  change MultilinearMap.alternatization A.toAlternatingMap.toMultilinearMap =
    (p.factorial : ℂ) • A.toAlternatingMap
  simpa only [Fintype.card_fin, Nat.cast_smul_eq_nsmul] using
    AlternatingMap.coe_alternatization A.toAlternatingMap

/-- A continuous alternating form on `Fin d → ℂ` is the finite coordinate-wedge expansion
of its values on the standard coordinate vectors. -/
lemma alternating_eq_sum_wedgeCovectors (d p : ℕ)
    (A : (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) :
    A = ∑ I : Fin p → Fin d,
      ((p.factorial : ℂ)⁻¹ * A (fun j ↦ Pi.single (I j) 1)) •
        wedgeCovectors (Fin d → ℂ) p
          (fun j ↦ ContinuousLinearMap.proj (I j)) := by
  classical
  have hM := multilinear_eq_sum_covectorProduct d p A.toContinuousMultilinearMap
  have hAlt := congrArg ContinuousMultilinearMap.alternatization hM
  rw [alternatization_toContinuousMultilinearMap d p A] at hAlt
  simp only [_root_.map_sum] at hAlt
  simp_rw [alternatization_smul, alternatization_covectorProduct] at hAlt
  change (p.factorial : ℂ) • A =
    ∑ I : Fin p → Fin d, A (fun j ↦ Pi.single (I j) 1) •
      wedgeCovectors (Fin d → ℂ) p
        (fun j ↦ ContinuousLinearMap.proj (I j)) at hAlt
  have hfac : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  calc
    A = (p.factorial : ℂ)⁻¹ • ((p.factorial : ℂ) • A) := by
      rw [← mul_smul, inv_mul_cancel₀ hfac, one_smul]
    _ = (p.factorial : ℂ)⁻¹ • ∑ I : Fin p → Fin d,
        A (fun j ↦ Pi.single (I j) 1) •
          wedgeCovectors (Fin d → ℂ) p
            (fun j ↦ ContinuousLinearMap.proj (I j)) := by rw [hAlt]
    _ = _ := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun I _ ↦ smul_smul _ _ _

/-- Evaluation at a fixed tuple is a continuous linear functional on continuous alternating
forms. -/
def alternatingFormEvaluation (d p : ℕ) (v : Fin p → Fin d → ℂ) :
    ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →L[ℂ] ℂ :=
  let L : ((Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun A ↦ A v
      map_add' := fun A B ↦ by simp
      map_smul' := fun a A ↦ by simp [ContinuousAlternatingMap.smul_apply] }
  LinearMap.mkContinuous L (∏ j, ‖v j‖) (fun A ↦ by
    change ‖A v‖ ≤ (∏ j, ‖v j‖) * ‖A‖
    simpa only [mul_comm] using A.le_opNorm v)

/-- The coefficient of an alternating form field in its finite coordinate-wedge expansion. -/
def coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (I : Fin p → Fin d) (y : Fin d → ℂ) : ℂ :=
  (p.factorial : ℂ)⁻¹ * θ y (fun j ↦ Pi.single (I j) 1)

lemma analyticOnNhd_coordinateCoefficient (d p : ℕ)
    (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    {s : Set (Fin d → ℂ)} (hθ : AnalyticOnNhd ℂ θ s) (I : Fin p → Fin d) :
    AnalyticOnNhd ℂ (coordinateCoefficient d p θ I) s := by
  let e : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  exact ((alternatingFormEvaluation d p e).comp_analyticOnNhd hθ).const_smul
    (c := (p.factorial : ℂ)⁻¹)

/-- A finite differential form whose fixed-chart evaluation is a given analytic
alternating-form field. -/
def formOfAnalyticField [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (chartSectionDomain X d U z)) :
    Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p :=
  ∑ I : Fin p → Fin d,
    Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p
      (holomorphicSectionOfChart X d U z hsource
        (coordinateCoefficient d p θ I)
        (analyticOnNhd_coordinateCoefficient d p θ hθ I))
      fun j ↦ chartCoordinateSection X d U z hsource (I j)

/-- The finite realization of an analytic alternating-form field evaluates to that field in the
chosen chart. -/
lemma chartEvaluation_formOfAnalyticField
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (hsource : ((Opposite.unop U : Opens (ComplexPoint X)) : Set _) ⊆
      (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) z).source)
    (p : ℕ) (θ : (Fin d → ℂ) → (Fin d → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (hθ : AnalyticOnNhd ℂ θ (chartSectionDomain X d U z)) :
    Set.EqOn (chartEvaluation X d U z p
      (formOfAnalyticField X d U z hsource p θ hθ)) θ
      (chartSectionDomain X d U z) := by
  intro y hy
  have hsum := map_sum (chartEvaluationAt X d U z p y)
    (fun I : Fin p → Fin d => Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p
      (holomorphicSectionOfChart X d U z hsource
        (coordinateCoefficient d p θ I)
        (analyticOnNhd_coordinateCoefficient d p θ hθ I))
      fun j ↦ chartCoordinateSection X d U z hsource (I j)) Finset.univ
  change chartEvaluationAt X d U z p y
    (formOfAnalyticField X d U z hsource p θ hθ) = _
  rw [formOfAnalyticField, hsum]
  have hterm : ∀ I : Fin p → Fin d,
      chartEvaluationAt X d U z p y
        (Algebra.DeRham.mk ℂ (OpenHolomorphicFunctions X d U) p
          (holomorphicSectionOfChart X d U z hsource
            (coordinateCoefficient d p θ I)
            (analyticOnNhd_coordinateCoefficient d p θ hθ I))
          fun j ↦ chartCoordinateSection X d U z hsource (I j)) =
      ((p.factorial : ℂ)⁻¹ * θ y fun j ↦ Pi.single (I j) 1) •
        wedgeCovectors (Fin d → ℂ) p fun j ↦ ContinuousLinearMap.proj (I j) := by
    intro I
    rw [show ((p.factorial : ℂ)⁻¹ * θ y fun j ↦ Pi.single (I j) 1) =
      coordinateCoefficient d p θ I y from rfl]
    change chartEvaluation X d U z p _ y = _
    rw [chartEvaluation_mk X d U z p _ _ hy]
    simp only [chartGeneratorEvaluation]
    rw [chartSection_holomorphicSectionOfChart X d U z hsource _ _ hy]
    have hd : (fun j ↦ chartSectionDifferential X d U z
        (chartCoordinateSection X d U z hsource (I j)) y) =
        fun j ↦ ContinuousLinearMap.proj (I j) := by
      funext j
      exact chartSectionDifferential_chartCoordinateSection X d U z hsource _ hy
    rw [hd]
  simp_rw [hterm]
  exact (alternating_eq_sum_wedgeCovectors d p (θ y)).symm

/-- A holomorphic section is complex analytic in every fixed chart. -/
lemma analyticOnNhd_chartSection [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (chartSection X d U z f)
      (chartSectionDomain X d U z) :=
  (isOpen_chartSectionDomain X d U z).analyticOn_iff_analyticOnNhd.mp
    (chartSection_contDiffOn X d U z f).analyticOn

/-- The coordinate differential of a holomorphic section is analytic. -/
lemma analyticOnNhd_chartSectionDifferential
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X)
    (f : OpenHolomorphicFunctions X d U) :
    AnalyticOnNhd ℂ (chartSectionDifferential X d U z f)
      (chartSectionDomain X d U z) := by
  refine AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z)
    (analyticOnNhd_chartSection X d U z f).fderiv fun y hy ↦ ?_
  rw [chartSectionDifferential,
    fderivWithin_of_isOpen (isOpen_chartSectionDomain X d U z) hy]

lemma analyticOnNhd_chartGeneratorEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (a₀ : OpenHolomorphicFunctions X d U) (w : Fin p → OpenHolomorphicFunctions X d U)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ
      (fun y ↦ chartGeneratorEvaluation X d U z p a₀ w y v)
      (chartSectionDomain X d U z) := by
  let s := chartSectionDomain X d U z
  have hentry (i j : Fin p) : AnalyticOnNhd ℂ
      (fun y ↦ chartSectionDifferential X d U z (w j) y (v i)) s :=
    (ContinuousLinearMap.apply ℂ ℂ (v i)).comp_analyticOnNhd
      (analyticOnNhd_chartSectionDifferential X d U z (w j))
  have hprod (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ ∏ j : Fin p,
        chartSectionDifferential X d U z (w (e j)) y (v j)) s :=
    Finset.univ.analyticOnNhd_fun_prod (fun j hj ↦ hentry j (e j))
  have hterm (e : Equiv.Perm (Fin p)) : AnalyticOnNhd ℂ
      (fun y ↦ (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        chartSectionDifferential X d U z (w (e j)) y (v j))) s := by
    convert (hprod e).const_smul (c := ((e.sign : ℤ) : ℂ)) using 1
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  have hdet : AnalyticOnNhd ℂ
      (fun y ↦ ∑ e : Equiv.Perm (Fin p), (((e.sign : ℤ) : ℂ) * ∏ j : Fin p,
        chartSectionDifferential X d U z (w (e j)) y (v j))) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun e he ↦ hterm e)
  have hmul := (analyticOnNhd_chartSection X d U z a₀).mul hdet
  refine AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z) hmul fun y _ ↦ ?_
  simp only [chartGeneratorEvaluation, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    wedgeCovectors_apply_eq_det, Matrix.det_apply]
  apply congrArg (chartSection X d U z a₀ y * ·)
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  rfl

lemma analyticOnNhd_chartEvaluation_apply
    [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p)
    (v : Fin p → Fin d → ℂ) :
    AnalyticOnNhd ℂ (fun y ↦ chartEvaluation X d U z p θ y v)
      (chartSectionDomain X d U z) := by
  induction θ using Algebra.DeRham.mk_induction with
  | mk a₀ w =>
      refine AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z)
        (analyticOnNhd_chartGeneratorEvaluation_apply X d U z p a₀ w v) fun y hy ↦ ?_
      rw [chartEvaluation_mk X d U z p a₀ w hy]
  | zero =>
      rw [chartEvaluation_zero]
      exact analyticOnNhd_const
  | add a b ha hb =>
      rw [chartEvaluation_add]
      convert ha.add hb using 1
      funext y
      simp
  | smul c a ha =>
      rw [chartEvaluation_smul]
      convert ha.const_smul (c := c) using 1
      funext y
      simp

/-- A holomorphic form has an analytic fixed-chart evaluation. -/
lemma analyticOnNhd_chartEvaluation [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (z : ComplexPoint X) (p : ℕ)
    (θ : Algebra.DeRham.Form ℂ (OpenHolomorphicFunctions X d U) p) :
    AnalyticOnNhd ℂ (chartEvaluation X d U z p θ)
      (chartSectionDomain X d U z) := by
  classical
  let s := chartSectionDomain X d U z
  let e (I : Fin p → Fin d) : Fin p → Fin d → ℂ := fun j ↦ Pi.single (I j) 1
  let W (I : Fin p → Fin d) :=
    wedgeCovectors (Fin d → ℂ) p (fun j ↦ ContinuousLinearMap.proj (I j))
  have hc (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ (p.factorial : ℂ)⁻¹ * chartEvaluation X d U z p θ y (e I)) s := by
    convert (analyticOnNhd_chartEvaluation_apply X d U z p θ (e I)).const_smul
      (c := (p.factorial : ℂ)⁻¹) using 1
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  have hterm (I : Fin p → Fin d) : AnalyticOnNhd ℂ
      (fun y ↦ ((p.factorial : ℂ)⁻¹ *
        chartEvaluation X d U z p θ y (e I)) • W I) s :=
    (hc I).smul analyticOnNhd_const
  have hsum : AnalyticOnNhd ℂ
      (fun y ↦ ∑ I : Fin p → Fin d,
        ((p.factorial : ℂ)⁻¹ * chartEvaluation X d U z p θ y (e I)) • W I) s :=
    Finset.univ.analyticOnNhd_fun_sum (fun I hI ↦ hterm I)
  exact AnalyticOnNhd.congr (isOpen_chartSectionDomain X d U z) hsum fun y _ ↦
    (alternating_eq_sum_wedgeCovectors d p (chartEvaluation X d U z p θ y)).symm

/-- Every open neighborhood contains a smaller neighborhood that is exactly a Euclidean ball in
the fixed chart at the chosen point. -/
lemma exists_chartBall_le [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U) :
    ∃ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (_i : U ⟶ V)
      (r : ℝ),
      x ∈ Opposite.unop V ∧ 0 < r ∧
      ((Opposite.unop V : Opens (ComplexPoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      chartSectionDomain X d V x =
        Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := by
  let e := localChart X d x
  have hxsource : x ∈ e.source := mem_localChart_source X d x
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _)) :=
    e.isOpen_inter_preimage_symm (Opposite.unop U).2
  have hximage : e x ∈ e.target ∩ e.symm ⁻¹' ((Opposite.unop U : Opens _) : Set _) := by
    refine ⟨e.map_source hxsource, ?_⟩
    rw [Set.mem_preimage, e.left_inv hxsource]
    exact hxU
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp (hopen.mem_nhds hximage)
  let Vo : Opens (ComplexPoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) r, e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxV : x ∈ Vo := ⟨hxsource, Metric.mem_ball_self hr⟩
  have hVU : Vo ≤ Opposite.unop U := by
    intro z hz
    have hzU : e.symm (e z) ∈ ((Opposite.unop U : Opens _) : Set _) := (hball hz.2).2
    rw [e.left_inv hz.1] at hzU
    exact hzU
  let V := Opposite.op Vo
  let i : U ⟶ V := (homOfLE hVU).op
  refine ⟨V, i, r, hxV, hr, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, chartAt_eq_localChart X d] using hz.1
  · unfold chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [V, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Vo : Set _) = Metric.ball (e x) r
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hytarget : y ∈ e.target := (hball hy).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Shrink a fixed chart ball to any smaller positive radius. -/
lemma exists_smaller_chartBall [SmoothOfRelativeDimension d X.hom]
    (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (r : ℝ)
    (hdom : chartSectionDomain X d V x =
      Metric.ball ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r)
    (ρ : NNReal) (hρ : 0 < ρ) (hρr : (ρ : ℝ) < r) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (_j : V ⟶ W),
      x ∈ Opposite.unop W ∧
      ((Opposite.unop W : Opens (ComplexPoint X)) : Set _) ⊆
        (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x).source ∧
      chartSectionDomain X d W x = Metric.ball
        ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := by
  let e := localChart X d x
  have hdom' : e.target ∩ e.symm ⁻¹' ((Opposite.unop V : Opens _) : Set _) =
      Metric.ball (e x) r := by
    unfold chartSectionDomain at hdom
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe] at hdom
    exact hdom
  have hxsource : x ∈ e.source := mem_localChart_source X d x
  let Wo : Opens (ComplexPoint X) :=
    ⟨e.source ∩ e ⁻¹' Metric.ball (e x) (ρ : ℝ),
      e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have hxW : x ∈ Wo := ⟨hxsource, Metric.mem_ball_self (by exact_mod_cast hρ)⟩
  have hWV : Wo ≤ Opposite.unop V := by
    intro z hz
    have hezdom : e z ∈ e.target ∩ e.symm ⁻¹'
        ((Opposite.unop V : Opens _) : Set _) :=
      hdom'.symm ▸ Metric.ball_subset_ball hρr.le hz.2
    have hzV := hezdom.2
    rw [Set.mem_preimage, e.left_inv hz.1] at hzV
    exact hzV
  let W := Opposite.op Wo
  let j : V ⟶ W := (homOfLE hWV).op
  refine ⟨W, j, hxW, ?_, ?_⟩
  · intro z hz
    simpa only [extChartAt_source, chartAt_eq_localChart X d] using hz.1
  · unfold chartSectionDomain
    simp only [extChartAt_target, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ, extChartAt_coe_symm, extChartAt_coe,
      Function.comp_id, chartAt_eq_localChart X d, modelWithCornersSelf_coe]
    dsimp only [W, Opposite.unop_op]
    change e.target ∩ e.symm ⁻¹' (Wo : Set _) = Metric.ball (e x) (ρ : ℝ)
    ext y
    constructor
    · rintro ⟨hytarget, hysource, hyball⟩
      rw [Set.mem_preimage, e.right_inv hytarget] at hyball
      exact hyball
    · intro hy
      have hyr : y ∈ Metric.ball (e x) r := Metric.ball_subset_ball hρr.le hy
      have hytarget : y ∈ e.target := (hdom'.symm ▸ hyr).1
      refine ⟨hytarget, e.map_target hytarget, ?_⟩
      rw [Set.mem_preimage, e.right_inv hytarget]
      exact hy

/-- Every closed holomorphic form of positive degree is locally exact. -/
theorem exists_local_holomorphicForm_primitive [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U) (p : ℕ)
    (form : HolomorphicForm X d U (p + 1))
    (hclosed : holomorphicFormDifferential X d U (p + 1) form = 0) :
    ∃ (W : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (k : U ⟶ W)
      (θ : HolomorphicForm X d W p),
      x ∈ Opposite.unop W ∧
      holomorphicFormDifferential X d W p θ =
        holomorphicFormRestriction X d k (p + 1) form := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U (p + 1)) form
  have hrel : Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d U) (p + 1) a ∈
      holomorphicFormRelations X d U (p + 2) := by
    change Submodule.Quotient.mk (Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d U) (p + 1) a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    exists_chartBall_le X d U x hxU
  let aV := formRestriction X d i (p + 1) a
  let η := chartEvaluation X d V x (p + 1) aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact analyticOnNhd_chartEvaluation X d V x (p + 1) aV
  have hrelV : Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d V) (p + 1) aV ∈
      holomorphicFormRelations X d V (p + 2) := by
    have h := formRestriction_mem_holomorphicFormRelations X d i (p + 2) hrel
    rwa [formRestriction_differential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hkernel : Algebra.DeRham.differential ℂ
        (OpenHolomorphicFunctions X d V) (p + 1) aV ∈
        restrictionStableAnalyticKernel X d V (p + 2) := by
      rw [← holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
      exact hrelV
    have hchart : chartEvaluation X d V x (p + 2)
        (Algebra.DeRham.differential ℂ
          (OpenHolomorphicFunctions X d V) (p + 1) aV) y = 0 := by
      have hk := hkernel
      rw [restrictionStableAnalyticKernel] at hk
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hk
      specialize hk V (𝟙 V)
      rw [formRestriction_id, LinearMap.id_apply] at hk
      exact (mem_chartEvaluationKernel_iff X d V (p + 2) _).1 hk x y hyV
    rw [chartEvaluation_differential X d V x (p + 1) aV hyV] at hchart
    have hwithin : extDerivWithin η (chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  obtain ⟨ρ, hρ, hρr, θfield, hθfield, hprim⟩ :=
    DifferentialForm.exists_analyticOnNhd_primitive_on_smaller_centered_ball p hr η hη hclosedη
  obtain ⟨W, j, hxW, hsourceW, hdomW⟩ :=
    exists_smaller_chartBall X d V x r hdomV ρ hρ hρr
  have hθW : AnalyticOnNhd ℂ θfield (chartSectionDomain X d W x) := by
    rw [hdomW]
    exact hθfield
  let b := formOfAnalyticField X d W x hsourceW p θfield hθW
  let θ : HolomorphicForm X d W p := Submodule.Quotient.mk b
  refine ⟨W, i ≫ j, θ, hxW, ?_⟩
  change Submodule.Quotient.mk (Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d W) p b) =
    Submodule.Quotient.mk (formRestriction X d (i ≫ j) (p + 1) a)
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d W (p + 1))).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply mem_restrictionStableAnalyticKernel_of_chartEvaluation_eq_zero
    X d W x (p + 1) hsourceW
  intro y hy
  rw [chartEvaluation_sub, Pi.sub_apply,
    chartEvaluation_differential X d W x p b hy,
    extDerivWithin_congr'
      (chartEvaluation_formOfAnalyticField X d W x hsourceW p θfield hθW) hy]
  have hwithin : extDerivWithin θfield (chartSectionDomain X d W x) y =
      extDeriv θfield y := by
    rw [extDerivWithin, extDeriv,
      fderivWithin_of_isOpen (isOpen_chartSectionDomain X d W x) hy]
  rw [hwithin]
  have hyball : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) (ρ : ℝ) := hdomW ▸ hy
  rw [hprim hyball, formRestriction_comp, LinearMap.comp_apply,
    chartEvaluation_formRestriction X d j x (p + 1) aV hy]
  simp [η]

/-- In degree zero, the Kähler representative of a scalar evaluates to the constant alternating
map with that scalar value. -/
lemma chartEvaluation_ofConstant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (c : ℂ) {y : Fin d → ℂ}
    (hy : y ∈ chartSectionDomain X d U x) :
    chartEvaluation X d U x 0
        (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d U) c) y =
      ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c := by
  rw [Algebra.DeRham.ofConstant_apply, Algebra.DeRham.ofFunction_apply,
    chartEvaluation_mk X d U x 0 _ _ hy]
  simp only [chartGeneratorEvaluation, chartSection_apply_of_mem X d U x _ hy]
  change c • wedgeCovectors (Fin d → ℂ) 0 Fin.elim0 = _
  ext v
  simp [wedgeCovectors]

/-- A closed holomorphic zero-form is locally the image of a complex constant. -/
theorem exists_local_holomorphicForm_eq_constant [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ)
    (x : ComplexPoint X) (hxU : x ∈ Opposite.unop U)
    (form : HolomorphicForm X d U 0)
    (hclosed : holomorphicFormDifferential X d U 0 form = 0) :
    ∃ (V : (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ) (i : U ⟶ V) (c : ℂ),
      x ∈ Opposite.unop V ∧
      holomorphicFormRestriction X d i 0 form =
        holomorphicFormOfConstant X d V c := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    (holomorphicFormRelations X d U 0) form
  have hrel : Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d U) 0 a ∈
      holomorphicFormRelations X d U 1 := by
    change Submodule.Quotient.mk (Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d U) 0 a) = 0 at hclosed
    rwa [Submodule.Quotient.mk_eq_zero] at hclosed
  obtain ⟨V, i, r, hxV, hr, hsourceV, hdomV⟩ :=
    exists_chartBall_le X d U x hxU
  let aV := formRestriction X d i 0 a
  let η := chartEvaluation X d V x 0 aV
  have hη : AnalyticOnNhd ℂ η (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    rw [← hdomV]
    exact analyticOnNhd_chartEvaluation X d V x 0 aV
  have hrelV : Algebra.DeRham.differential ℂ
      (OpenHolomorphicFunctions X d V) 0 aV ∈
      holomorphicFormRelations X d V 1 := by
    have h := formRestriction_mem_holomorphicFormRelations X d i 1 hrel
    rwa [formRestriction_differential] at h
  have hclosedη : Set.EqOn (extDeriv η) 0 (Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r) := by
    intro y hy
    have hyV : y ∈ chartSectionDomain X d V x := hdomV.symm ▸ hy
    have hkernel : Algebra.DeRham.differential ℂ
        (OpenHolomorphicFunctions X d V) 0 aV ∈
        restrictionStableAnalyticKernel X d V 1 := by
      rw [← holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
      exact hrelV
    have hchart : chartEvaluation X d V x 1
        (Algebra.DeRham.differential ℂ
          (OpenHolomorphicFunctions X d V) 0 aV) y = 0 := by
      have hk := hkernel
      rw [restrictionStableAnalyticKernel] at hk
      simp only [Submodule.mem_iInf, Submodule.mem_comap] at hk
      specialize hk V (𝟙 V)
      rw [formRestriction_id, LinearMap.id_apply] at hk
      exact (mem_chartEvaluationKernel_iff X d V 1 _).1 hk x y hyV
    rw [chartEvaluation_differential X d V x 0 aV hyV] at hchart
    have hwithin : extDerivWithin η (chartSectionDomain X d V x) y =
        extDeriv η y := by
      rw [extDerivWithin, extDeriv,
        fderivWithin_of_isOpen (isOpen_chartSectionDomain X d V x) hyV]
    rwa [hwithin] at hchart
  have hconst :=
    DifferentialForm.zeroForm_eq_at_center_of_closedOn_ball hr η hη hclosedη
  let center := (extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x
  let c := DifferentialForm.zeroFormCoeff η center
  refine ⟨V, i, c, hxV, ?_⟩
  change Submodule.Quotient.mk aV = Submodule.Quotient.mk
    (Algebra.DeRham.ofConstant ℂ (OpenHolomorphicFunctions X d V) c)
  apply (Submodule.Quotient.eq (holomorphicFormRelations X d V 0)).2
  rw [holomorphicFormRelations_eq_restrictionStableAnalyticKernel]
  apply mem_restrictionStableAnalyticKernel_of_chartEvaluation_eq_zero
    X d V x 0 hsourceV
  intro y hy
  rw [chartEvaluation_sub, Pi.sub_apply]
  have hyball' : y ∈ Metric.ball
      ((extChartAt (modelWithCornersSelf ℂ (Fin d → ℂ)) x) x) r := hdomV ▸ hy
  have hyball : y ∈ Metric.ball center r := by simpa only [center] using hyball'
  rw [show chartEvaluation X d V x 0 aV y = η center from hconst hyball]
  rw [chartEvaluation_ofConstant X d V x c hy]
  have hrepr := congrFun (DifferentialForm.zeroForm_eq_constOfIsEmpty η) center
  change η center =
    ContinuousAlternatingMap.constOfIsEmpty ℂ (Fin d → ℂ) (Fin 0) c at hrepr
  rw [hrepr]
  exact sub_self _

end AlgebraicGeometry.ComplexPoint
