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

public import FormalConjecturesForMathlib.AlgebraicTopology.ComplexDifferentiableLocalClassInvariance
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Chart-local class invariance under a differentiable transition germ

This file turns the local nonlinear degree calculation into a chart-comparison theorem.  For two
complex charts through the same point, their compressed inverse-chart embeddings determine an
actual open partial homeomorphism of `ℂᵈ`.  If its derivative at the model origin is injective
and complex linear, the two explicitly normalized chart-local homology classes agree.

The proof constructs the overlap neighborhood, uses point excision to lift the standard class,
and proves the factorization through the transition as an equality of maps of topological pairs.
Thus no chart-compatibility or local-degree statement is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter Set Asymptotics

namespace AlgebraicTopology.Singular

variable {M : Type} [TopologicalSpace M]
variable (d : ℕ)

/-! ## Complex derivatives of the radial chart compression -/

/-- On a finite complex pi space, the product topology used by manifold charts agrees with the
topology induced by the sup norm used by Fréchet-calculus composition lemmas. -/
lemma piHasFDerivAt_iff_normed
    (f : (Fin d → ℂ) → (Fin d → ℂ))
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (x : Fin d → ℂ) :
    @HasFDerivAt ℂ _ (Fin d → ℂ) Pi.addCommGroup (Pi.Function.module (Fin d) ℂ ℂ)
      Pi.topologicalSpace (Fin d → ℂ) Pi.addCommGroup
      (Pi.Function.module (Fin d) ℂ ℂ) Pi.topologicalSpace f L x ↔
    @HasFDerivAt ℂ _ (Fin d → ℂ) Pi.normedAddCommGroup.toAddCommGroup
      Pi.normedSpace.toModule PseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Fin d → ℂ) Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace f L x := by
  rfl

private lemma hasFDerivAt_univUnitBall_formula_normed :
    HasFDerivAt (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹ • x)
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have ha : Tendsto (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) (nhds 0) (nhds 1) := by
    have hac : ContinuousAt (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) 0 := by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    have hzero : (√(1 + ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹ = (1 : ℝ) := by norm_num
    change Tendsto (fun x : Fin d → ℂ ↦ (√(1 + ‖x‖ ^ 2))⁻¹) (nhds 0)
      (nhds ((√(1 + ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹)) at hac
    rw [hzero] at hac
    exact hac
  have hsmall : ∀ᶠ x : Fin d → ℂ in nhds 0,
      |(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| < ε := by
    have hball := ha.eventually (Metric.ball_mem_nhds (1 : ℝ) hε)
    filter_upwards [hball] with x hx
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hsmall] with x hx
  simp only [ContinuousLinearMap.id_apply]
  norm_num
  change ‖(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ • x - x‖ ≤ ε * ‖x‖
  calc
    ‖(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ • x - x‖ =
        ‖((√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1) • x‖ := by rw [sub_smul, one_smul]
    _ = |(√(1 + ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hx.le (norm_nonneg x)

private lemma hasFDerivAt_univUnitBall_symm_formula_normed :
    HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm :
      (Fin d → ℂ) → (Fin d → ℂ))
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have ha : Tendsto (fun x : Fin d → ℂ ↦ (√(1 - ‖x‖ ^ 2))⁻¹) (nhds 0) (nhds 1) := by
    have hac : ContinuousAt (fun x : Fin d → ℂ ↦ (√(1 - ‖x‖ ^ 2))⁻¹) 0 := by
      apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    have hzero : (√(1 - ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹ = (1 : ℝ) := by norm_num
    change Tendsto (fun x : Fin d → ℂ ↦ (√(1 - ‖x‖ ^ 2))⁻¹) (nhds 0)
      (nhds ((√(1 - ‖(0 : Fin d → ℂ)‖ ^ 2))⁻¹)) at hac
    rw [hzero] at hac
    exact hac
  have hsmall : ∀ᶠ x : Fin d → ℂ in nhds 0,
      |(√(1 - ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| < ε := by
    have hball := ha.eventually (Metric.ball_mem_nhds (1 : ℝ) hε)
    filter_upwards [hball] with x hx
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hsmall] with x hx
  simp only [OpenPartialHomeomorph.univUnitBall_symm_apply,
    ContinuousLinearMap.id_apply]
  norm_num
  change ‖(√(1 - ‖x‖ ^ (2 : ℕ)))⁻¹ • x - x‖ ≤ ε * ‖x‖
  calc
    ‖(√(1 - ‖x‖ ^ (2 : ℕ)))⁻¹ • x - x‖ =
        ‖((√(1 - ‖x‖ ^ (2 : ℕ)))⁻¹ - 1) • x‖ := by rw [sub_smul, one_smul]
    _ = |(√(1 - ‖x‖ ^ (2 : ℕ)))⁻¹ - 1| * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hx.le (norm_nonneg x)

/-- The positive-radius radial chart compression has derivative `r · id` at the model origin.
This is complex differentiability at the origin only; the norm-dependent map is not asserted to
be holomorphic away from the origin. -/
lemma hasFDerivAt_univBall_complex (c : Fin d → ℂ) (r : ℝ) (hr : 0 < r) :
    HasFDerivAt (OpenPartialHomeomorph.univBall c r :
      (Fin d → ℂ) → (Fin d → ℂ))
      ((r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)) 0 := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr]
  apply (piHasFDerivAt_iff_normed d _ _ _).mpr
  apply ((hasFDerivAt_univUnitBall_formula_normed d).const_smul (r : ℂ)).add_const c
    |>.congr_of_eventuallyEq
  filter_upwards [] with y
  change r • OpenPartialHomeomorph.univUnitBall y + c =
    (r : ℂ) • ((√(1 + ‖y‖ ^ 2))⁻¹ • y) + c
  rw [OpenPartialHomeomorph.univUnitBall_apply]
  match_scalars
  all_goals rfl

/-- The inverse positive-radius radial compression has derivative `r⁻¹ · id` at its center. -/
lemma hasFDerivAt_univBall_symm_complex (c : Fin d → ℂ) (r : ℝ) (hr : 0 < r) :
    HasFDerivAt ((OpenPartialHomeomorph.univBall c r).symm :
      (Fin d → ℂ) → (Fin d → ℂ))
      ((ContinuousLinearMap.id ℂ (Fin d → ℂ)).comp
        ((r⁻¹ : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ))) c := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr]
  apply (piHasFDerivAt_iff_normed d _ _ _).mpr
  have ha : HasFDerivAt
      (fun y : Fin d → ℂ ↦ (r⁻¹ : ℂ) • (y - c))
      ((r⁻¹ : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)) c :=
    ((hasFDerivAt_id c).sub_const c).const_smul (r⁻¹ : ℂ)
  have hg : HasFDerivAt (OpenPartialHomeomorph.univUnitBall.symm :
      (Fin d → ℂ) → (Fin d → ℂ))
      (ContinuousLinearMap.id ℂ (Fin d → ℂ)) ((r⁻¹ : ℂ) • (c - c)) := by
    simpa using (hasFDerivAt_univUnitBall_symm_formula_normed d)
  apply (hg.comp c ha).congr_of_eventuallyEq
  filter_upwards [] with y
  change OpenPartialHomeomorph.univUnitBall.symm (r⁻¹ • (y - c)) =
    OpenPartialHomeomorph.univUnitBall.symm ((r⁻¹ : ℂ) • (y - c))
  congr 1
  match_scalars
  all_goals rfl

/-- The matrix of a complex continuous-linear endomorphism in the standard basis of a pi space. -/
def complexMatrixOfContinuousLinearMap
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toMatrix' L.toLinearMap

@[simp]
lemma complexMatrixOfContinuousLinearMap_mulVec
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (v : Fin d → ℂ) :
    (complexMatrixOfContinuousLinearMap d L).mulVec v = L v :=
  LinearMap.toMatrix'_mulVec L.toLinearMap v

lemma complexMatrixOfContinuousLinearMap_det_ne_zero
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) (hL : Function.Injective L) :
    (complexMatrixOfContinuousLinearMap d L).det ≠ 0 := by
  let A := complexMatrixOfContinuousLinearMap d L
  have hAinj : Function.Injective A.mulVec := by
    intro x y hxy
    apply hL
    simpa only [A, complexMatrixOfContinuousLinearMap_mulVec] using hxy
  have hAunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hAinj
  exact (A.isUnit_iff_isUnit_det.mp hAunit).ne_zero

/-- The coordinate transition between the two compressed inverse-chart embeddings used to define
`localClassOfChart`. -/
def compressedChartTransition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ) :=
  (chartModelEmbedding d e x hx).trans (chartModelEmbedding d e' x hx').symm

lemma zero_mem_compressedChartTransition_source
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    0 ∈ (compressedChartTransition d e e' x hx hx').source := by
  rw [compressedChartTransition, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · rw [chartModelEmbedding_source]
    trivial
  · change chartModelEmbedding d e x hx 0 ∈ (chartModelEmbedding d e' x hx').target
    rw [chartModelEmbedding_zero]
    have htarget : chartModelEmbedding d e' x hx' 0 ∈
        (chartModelEmbedding d e' x hx').target :=
      (chartModelEmbedding d e' x hx').map_source (by
      rw [chartModelEmbedding_source]
      trivial)
    simpa only [chartModelEmbedding_zero] using htarget

@[simp]
lemma compressedChartTransition_zero
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    compressedChartTransition d e e' x hx hx' 0 = 0 := by
  change (chartModelEmbedding d e' x hx').symm
    (chartModelEmbedding d e x hx 0) = 0
  rw [chartModelEmbedding_zero]
  have hleft := (chartModelEmbedding d e' x hx').left_inv
    (show 0 ∈ (chartModelEmbedding d e' x hx').source by
      rw [chartModelEmbedding_source]
      trivial)
  simpa only [chartModelEmbedding_zero] using hleft

/-- On a subset of the transition domain, applying the transition and then the second compressed
chart embedding is exactly the first compressed chart embedding, as maps of point-complement
pairs. -/
lemma complexNeighborhoodPuncturedPairMap_compressedChartTransition_comp
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (V : Set (Fin d → ℂ))
    (hV : V ⊆ (compressedChartTransition d e e' x hx hx').source)
    (hf_ne : ∀ z, z ∈ V → z ≠ 0 →
      compressedChartTransition d e e' x hx hx' z ≠ 0) :
    complexNeighborhoodPuncturedPairMapOf d V
        (compressedChartTransition d e e' x hx hx')
        ((compressedChartTransition d e e' x hx hx').continuousOn.mono hV)
        (compressedChartTransition_zero d e e' x hx hx') hf_ne ≫
      chartModelEmbeddingPair d e' x hx' =
    neighborhoodPointComplementPairMap V 0 ≫ chartModelEmbeddingPair d e x hx := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change chartModelEmbedding d e' x hx'
        ((chartModelEmbedding d e' x hx').symm (chartModelEmbedding d e x hx z.1.1)) =
      chartModelEmbedding d e x hx z.1.1
    exact (chartModelEmbedding d e' x hx').right_inv (hV z.1.2).2
  · apply ConcreteCategory.hom_ext
    intro z
    change chartModelEmbedding d e' x hx'
        ((chartModelEmbedding d e' x hx').symm (chartModelEmbedding d e x hx z.1)) =
      chartModelEmbedding d e x hx z.1
    exact (chartModelEmbedding d e' x hx').right_inv (hV z.2).2

/-- Differentiability with injective complex derivative of the actual compressed chart transition
implies equality of the two normalized chart-local fundamental classes. -/
theorem localClassOfChart_eq_of_hasFDerivAt_compressedTransition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (L : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hL : Function.Injective L)
    (hderiv : HasFDerivAt (compressedChartTransition d e e' x hx hx') L 0) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  let f := compressedChartTransition d e e' x hx hx'
  let A := complexMatrixOfContinuousLinearMap d L
  have hA : A.det ≠ 0 := complexMatrixOfContinuousLinearMap_det_ne_zero d L hL
  have hAL : (A.mulVecLin.toContinuousLinearMap :
      (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = L :=
    ContinuousLinearMap.ext (complexMatrixOfContinuousLinearMap_mulVec d L)
  have hderivA : HasFDerivAt f
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 := by
    rw [hAL]
    exact hderiv
  obtain ⟨V, hVsource, hf_ne, hVopen, h0V, hlocal⟩ :=
    exists_open_complexDifferentiable_localClass_invariance d A hA f.source f.open_source
      (zero_mem_compressedChartTransition_source d e e' x hx hx') f f.continuousOn
      (compressedChartTransition_zero d e e' x hx hx') hderivA
  obtain ⟨c, hc⟩ := neighborhoodPointComplement_relativeHomologyMap_surjective
    V 0 hVopen h0V (2 * d) (standardComplexLocalClass d)
  have hfc : relativeHomologyMap ℚ (2 * d)
      (complexNeighborhoodPuncturedPairMapOf d V f
        (f.continuousOn.mono hVsource) (compressedChartTransition_zero d e e' x hx hx') hf_ne) c =
      standardComplexLocalClass d := hlocal c hc
  have hpair := complexNeighborhoodPuncturedPairMap_compressedChartTransition_comp
    d e e' x hx hx' V hVsource hf_ne
  unfold localClassOfChart
  calc
    relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)
        (standardComplexLocalClass d) =
        relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e x hx)
          (relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap V 0) c) := by
            rw [hc]
    _ = relativeHomologyMap ℚ (2 * d)
        (neighborhoodPointComplementPairMap V 0 ≫ chartModelEmbeddingPair d e x hx) c := by
          rw [relativeHomologyMap_comp]
          rfl
    _ = relativeHomologyMap ℚ (2 * d)
        (complexNeighborhoodPuncturedPairMapOf d V f
            (f.continuousOn.mono hVsource)
            (compressedChartTransition_zero d e e' x hx hx') hf_ne ≫
          chartModelEmbeddingPair d e' x hx') c := by rw [hpair]
    _ = relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e' x hx')
        (relativeHomologyMap ℚ (2 * d)
          (complexNeighborhoodPuncturedPairMapOf d V f
            (f.continuousOn.mono hVsource)
            (compressedChartTransition_zero d e e' x hx hx') hf_ne) c) := by
              rw [relativeHomologyMap_comp]
              rfl
    _ = relativeHomologyMap ℚ (2 * d) (chartModelEmbeddingPair d e' x hx')
        (standardComplexLocalClass d) := by rw [hfc]

/-- It is enough to differentiate the ordinary coordinate transition.  The derivatives of both
radial compression factors in `chartModelEmbedding` are inserted automatically, and their
positive radii make them injective. -/
theorem localClassOfChart_eq_of_hasFDerivAt_transition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (T : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ))
    (hT : Function.Injective T)
    (hderiv : HasFDerivAt (fun v ↦ e' (e.symm v)) T (e x)) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  let r := chartRadius d e x hx
  let r' := chartRadius d e' x hx'
  let L₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (r : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ)
  let L₂ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    (ContinuousLinearMap.id ℂ (Fin d → ℂ)).comp
      ((r'⁻¹ : ℂ) • ContinuousLinearMap.id ℂ (Fin d → ℂ))
  let L := L₂.comp (T.comp L₀)
  have hfirst : HasFDerivAt
      (OpenPartialHomeomorph.univBall (e x) r :
        (Fin d → ℂ) → (Fin d → ℂ)) L₀ 0 :=
    hasFDerivAt_univBall_complex d (e x) r (chartRadius_pos d e x hx)
  have hlast : HasFDerivAt
      ((OpenPartialHomeomorph.univBall (e' x) r').symm :
        (Fin d → ℂ) → (Fin d → ℂ)) L₂ (e' x) :=
    hasFDerivAt_univBall_symm_complex d (e' x) r' (chartRadius_pos d e' x hx')
  have hfirstN := (piHasFDerivAt_iff_normed d _ L₀ 0).mp hfirst
  have hderivN := (piHasFDerivAt_iff_normed d _ T (e x)).mp hderiv
  have hlastN := (piHasFDerivAt_iff_normed d _ L₂ (e' x)).mp hlast
  have hderivAt : HasFDerivAt (fun v ↦ e' (e.symm v)) T
      (OpenPartialHomeomorph.univBall (e x) r 0) := by
    simpa only [OpenPartialHomeomorph.univBall_apply_zero] using hderivN
  have hmiddle := hderivAt.comp 0 hfirstN
  have hcenter :
      e' (e.symm (OpenPartialHomeomorph.univBall (e x) r 0)) = e' x := by
    rw [OpenPartialHomeomorph.univBall_apply_zero, e.left_inv hx]
  have hlastAt : HasFDerivAt
      ((OpenPartialHomeomorph.univBall (e' x) r').symm :
        (Fin d → ℂ) → (Fin d → ℂ)) L₂
      (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r 0))) := by
    rw [hcenter]
    exact hlastN
  have hcomposedN : HasFDerivAt
      (fun v ↦ (OpenPartialHomeomorph.univBall (e' x) r').symm
        (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r v)))) L 0 := by
    simpa only [L, Function.comp_def] using hlastAt.comp 0 hmiddle
  have hcomposed := (piHasFDerivAt_iff_normed d _ L 0).mpr hcomposedN
  have htransition : HasFDerivAt
      (compressedChartTransition d e e' x hx hx') L 0 := by
    apply hcomposed.congr_of_eventuallyEq
    filter_upwards [] with v
    change (chartModelEmbedding d e' x hx').symm
        (chartModelEmbedding d e x hx v) =
      (OpenPartialHomeomorph.univBall (e' x) r').symm
        (e' (e.symm (OpenPartialHomeomorph.univBall (e x) r v)))
    rfl
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast (chartRadius_pos d e x hx).ne'
  have hr' : (r'⁻¹ : ℂ) ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (chartRadius_pos d e' x hx').ne')
  have hL₀ : Function.Injective L₀ := by
    intro a b hab
    apply smul_right_injective (Fin d → ℂ) hr
    simpa only [L₀, smul_apply, ContinuousLinearMap.id_apply] using hab
  have hL₂ : Function.Injective L₂ := by
    intro a b hab
    apply smul_right_injective (Fin d → ℂ) hr'
    simpa only [L₂, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply] using hab
  have hL : Function.Injective L := by
    intro a b hab
    apply hL₀
    apply hT
    apply hL₂
    simpa only [L, ContinuousLinearMap.comp_apply] using hab
  exact localClassOfChart_eq_of_hasFDerivAt_compressedTransition
    d e e' x hx hx' L hL htransition

/-- Two charts give the same normalized local class when their coordinate transition and its
inverse are complex analytic at the distinguished point.  Injectivity of the forward derivative
is proved by differentiating the local inverse identity; it is not an additional premise. -/
theorem localClassOfChart_eq_of_analyticAt_transition
    (e e' : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (hx' : x ∈ e'.source)
    (hf : AnalyticAt ℂ (fun v ↦ e' (e.symm v)) (e x))
    (hg : AnalyticAt ℂ (fun v ↦ e (e'.symm v)) (e' x)) :
    localClassOfChart d e x hx = localClassOfChart d e' x hx' := by
  let f : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ e' (e.symm v)
  let g : (Fin d → ℂ) → (Fin d → ℂ) := fun v ↦ e (e'.symm v)
  let T := fderiv ℂ f (e x)
  let S := fderiv ℂ g (e' x)
  have hfN : HasFDerivAt f T (e x) := hf.differentiableAt.hasFDerivAt
  have hgN : HasFDerivAt g S (e' x) := hg.differentiableAt.hasFDerivAt
  have hfx : f (e x) = e' x := by
    change e' (e.symm (e x)) = e' x
    rw [e.left_inv hx]
  have hgAt : HasFDerivAt g S (f (e x)) := by
    rw [hfx]
    exact hgN
  have hcomp : HasFDerivAt (g ∘ f) (S.comp T) (e x) := hgAt.comp (e x) hfN
  let t := e.symm.trans e'
  have hsource : e x ∈ t.source := by
    change e x ∈ (e.symm.trans e').source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  have hlocalInverse : (g ∘ f) =ᶠ[nhds (e x)] id := by
    filter_upwards [t.open_source.mem_nhds hsource] with v hv
    change t.symm (t v) = v
    exact t.left_inv hv
  have hcompId : HasFDerivAt id (S.comp T) (e x) :=
    hcomp.congr_of_eventuallyEq hlocalInverse.symm
  have hST : S.comp T = ContinuousLinearMap.id ℂ (Fin d → ℂ) :=
    hcompId.unique (hasFDerivAt_id (e x))
  have hT : Function.Injective T := by
    intro a b hab
    calc
      a = (S.comp T) a := by rw [hST, ContinuousLinearMap.id_apply]
      _ = (S.comp T) b := congrArg S hab
      _ = b := by rw [hST, ContinuousLinearMap.id_apply]
  have hfP : HasFDerivAt f T (e x) :=
    (piHasFDerivAt_iff_normed d f T (e x)).mpr hfN
  exact localClassOfChart_eq_of_hasFDerivAt_transition d e e' x hx hx' T hT hfP

end AlgebraicTopology.Singular
