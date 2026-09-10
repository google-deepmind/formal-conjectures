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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ClosedImmersionAnalyticLeftInverse
public import FormalConjecturesForMathlib.AlgebraicGeometry.ClosedImmersionComplexPoint
public import FormalConjecturesForMathlib.AlgebraicTopology.SplitDerivativeNormalChart

/-!
# Constructed normal coordinates for smooth closed immersions

The derivative projection here comes from lifted algebraic coordinate sections. The normal
chart is then constructed by the inverse function theorem. Finally the actual topological
embedding theorem excludes remote branches and identifies the whole local analytic support
with zero normal coordinate. No analytic immersion or flattening equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

/-- The actual derivative left inverse obtained from lifted intrinsic coordinates. -/
def closedImmersionDerivativeProjection : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ) :=
  (exists_leftInverse_fderiv_inclusionInComplexCharts
    X Y i m d z).choose

theorem closedImmersionDerivativeProjection_leftInverse :
    (closedImmersionDerivativeProjection X Y i m d z).comp
      (fderiv ℂ (inclusionInComplexCharts X Y i m d z)
        (localChart Y m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) :=
  (exists_leftInverse_fderiv_inclusionInComplexCharts
    X Y i m d z).choose_spec

/-- Actual normal-coordinate parametrization, with the kernel of the constructed
derivative projection as its complex normal space. -/
def closedImmersionNormalChart :
    OpenPartialHomeomorph
      ((Fin m → ℂ) ×
        (closedImmersionDerivativeProjection X Y i m d z).ker)
      (Fin d → ℂ) :=
  (analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt.normalChart
    (closedImmersionDerivativeProjection X Y i m d z)
    (closedImmersionDerivativeProjection_leftInverse X Y i m d z)

@[simp] theorem closedImmersionNormalChart_apply
    (v : (Fin m → ℂ) ×
      (closedImmersionDerivativeProjection X Y i m d z).ker) :
    closedImmersionNormalChart X Y i m d z v =
      inclusionInComplexCharts X Y i m d z v.1 + v.2 := rfl

theorem closedImmersionNormalChart_mem_source :
    (localChart Y m z z, 0) ∈
      (closedImmersionNormalChart X Y i m d z).source :=
  (analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt.normalChart_mem_source _ _

theorem closedImmersionNormalChart_mem_target :
    localChart X d (Point.map i z) (Point.map i z) ∈
      (closedImmersionNormalChart X Y i m d z).target := by
  simpa only [closedImmersionNormalChart, inclusionInComplexCharts_at_center] using
    (analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt.normalChart_mem_target
      (closedImmersionDerivativeProjection X Y i m d z)
      (closedImmersionDerivativeProjection_leftInverse X Y i m d z)

@[simp] theorem closedImmersionNormalChart_symm_center :
    (closedImmersionNormalChart X Y i m d z).symm
      (localChart X d (Point.map i z) (Point.map i z)) =
        (localChart Y m z z, 0) := by
  simpa using
    (closedImmersionNormalChart X Y i m d z).left_inv
      (closedImmersionNormalChart_mem_source X Y i m d z)

/-- The normal space has the actual complex codimension, by the constructed linear
splitting; algebraic dimension is not substituted for a topological dimension theorem. -/
theorem closedImmersionNormalKernel_finrank :
    Module.finrank ℂ
      (closedImmersionDerivativeProjection X Y i m d z).ker =
        d - m := by
  have hdim :=
    ((fderiv ℂ (inclusionInComplexCharts X Y i m d z)
      (localChart Y m z z)).splitKernelEquiv
      (closedImmersionDerivativeProjection X Y i m d z)
      (closedImmersionDerivativeProjection_leftInverse X Y i m d z)).toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- The constructed normal parametrization is complex analytic at its center. -/
theorem analyticAt_closedImmersionNormalChart :
    AnalyticAt ℂ (closedImmersionNormalChart X Y i m d z)
      (localChart Y m z z, 0) := by
  let P := closedImmersionDerivativeProjection X Y i m d z
  change AnalyticAt ℂ
    (fun v : (Fin m → ℂ) × P.ker =>
      inclusionInComplexCharts X Y i m d z v.1 + v.2) _
  exact ((analyticAt_inclusionInComplexCharts X Y i m d z).comp
    (f := (ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker))
    (x := (localChart Y m z z, 0))
    ((ContinuousLinearMap.fst ℂ (Fin m → ℂ) P.ker).analyticAt _)).add
      ((P.ker.subtypeL.analyticAt _).comp
        ((ContinuousLinearMap.snd ℂ (Fin m → ℂ) P.ker).analyticAt _))

/-- The inverse normal coordinates are complex analytic as well, by the analytic inverse
function theorem applied to the actual invertible complex derivative. -/
theorem analyticAt_closedImmersionNormalChart_symm :
    AnalyticAt ℂ (closedImmersionNormalChart X Y i m d z).symm
      (localChart X d (Point.map i z) (Point.map i z)) := by
  let P := closedImmersionDerivativeProjection X Y i m d z
  let : CompleteSpace P.ker := FiniteDimensional.complete ℂ P.ker
  let e := closedImmersionNormalChart X Y i m d z
  have ha := analyticAt_inclusionInComplexCharts X Y i m d z
  have hd := ha.hasStrictFDerivAt.add_kernel P
    (closedImmersionDerivativeProjection_leftInverse X Y i m d z)
  have hder : fderiv ℂ e (localChart Y m z z, 0) =
      ((fderiv ℂ (inclusionInComplexCharts X Y i m d z)
        (localChart Y m z z)).splitKernelEquiv P
        (closedImmersionDerivativeProjection_leftInverse X Y i m d z)).toContinuousLinearMap :=
    hd.hasFDerivAt.fderiv
  have h := e.analyticAt_symm'
    (closedImmersionNormalChart_mem_source X Y i m d z)
    (analyticAt_closedImmersionNormalChart X Y i m d z) hder
  simpa only [e, closedImmersionNormalChart_apply, Submodule.coe_zero, add_zero,
    inclusionInComplexCharts_at_center] using h

/-- Near the selected ambient point, membership in the entire actual image is equivalent
to having zero normal coordinate. The forward direction uses the proved induced topology
to exclude image points whose intrinsic parameters are outside the coordinate neighborhood. -/
theorem eventually_mem_range_iff_normal_eq_zero :
    ∀ᶠ y in 𝓝 (Point.map i z),
      y ∈ Set.range (Point.map i) ↔
        ((closedImmersionNormalChart X Y i m d z).symm
          (localChart X d (Point.map i z) y)).2 = 0 := by
  let eY := localChart Y m z
  let eX := localChart X d (Point.map i z)
  let eN := closedImmersionNormalChart X Y i m d z
  let g := Point.map i
  have hzY : z ∈ eY.source := mem_localChart_source Y m z
  have hzX : g z ∈ eX.source := mem_localChart_source X d (g z)
  have hzN : (eY z, 0) ∈ eN.source :=
    closedImmersionNormalChart_mem_source X Y i m d z
  have hzNt : eX (g z) ∈ eN.target :=
    closedImmersionNormalChart_mem_target X Y i m d z
  have hcenter : eN.symm (eX (g z)) = (eY z, 0) :=
    closedImmersionNormalChart_symm_center X Y i m d z
  have hparam : ∀ᶠ w in 𝓝 z, w ∈ eY.source ∧ (eY w, 0) ∈ eN.source := by
    filter_upwards [eY.open_source.mem_nhds hzY,
      ((eY.continuousAt hzY).prodMk continuousAt_const)
        (eN.open_source.mem_nhds hzN)] with w hwY hwN
    exact ⟨hwY, hwN⟩
  rw [(isInducing_map_of_closedImmersion i).nhds_eq_comap z, eventually_comap] at hparam
  have hN : ∀ᶠ y in 𝓝 (g z), eX y ∈ eN.target :=
    (eX.continuousAt hzX) (eN.open_target.mem_nhds hzNt)
  have hc : ContinuousAt (fun y => (eN.symm (eX y)).1) (g z) :=
    ((eN.continuousAt_symm hzNt).comp (eX.continuousAt hzX)).fst
  have hback : ∀ᶠ y in 𝓝 (g z),
      g (eY.symm (eN.symm (eX y)).1) ∈ eX.source := by
    have hcont : ContinuousAt (fun y => g (eY.symm (eN.symm (eX y)).1)) (g z) := by
      apply (Point.continuous_map i).continuousAt.comp
      apply ContinuousAt.comp _ hc
      change ContinuousAt eY.symm (eN.symm (eX (g z))).1
      rw [hcenter]
      exact eY.continuousAt_symm (eY.map_source hzY)
    apply hcont (eX.open_source.mem_nhds _)
    change g (eY.symm (eN.symm (eX (g z))).1) ∈ eX.source
    rw [hcenter, eY.left_inv hzY]
    exact hzX
  filter_upwards [hparam, hN, hback, eX.open_source.mem_nhds hzX] with y hpre hyN hyback hyX
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨hwY, hwN⟩ := hpre w rfl
    have hφ : eN (eY w, 0) = eX (g w) := by
      change eX (g (eY.symm (eY w))) + 0 = _
      rw [eY.left_inv hwY, add_zero]
    have heq := eN.left_inv hwN
    rw [hφ] at heq
    exact congrArg Prod.snd heq
  · intro hn
    change (eN.symm (eX y)).2 = 0 at hn
    refine ⟨eY.symm (eN.symm (eX y)).1, ?_⟩
    apply eX.injOn hyback hyX
    have hright := eN.right_inv hyN
    change eX (g (eY.symm (eN.symm (eX y)).1)) + (eN.symm (eX y)).2 = eX y at hright
    rw [hn] at hright
    simpa only [Submodule.coe_zero, add_zero] using hright

/-- An actual open ambient neighborhood on which normal coordinates detect the full
closed-immersion image, extracted from the proved neighborhood assertion. -/
theorem exists_open_normalCriterion :
    ∃ W : Set (ComplexPoint X), IsOpen W ∧ Point.map i z ∈ W ∧
      ∀ y ∈ W, y ∈ Set.range (Point.map i) ↔
        ((closedImmersionNormalChart X Y i m d z).symm
          (localChart X d (Point.map i z) y)).2 = 0 := by
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp
    (eventually_mem_range_iff_normal_eq_zero X Y i m d z)
  exact ⟨W, hWopen, hzW, hWsub⟩

/-- The ambient flattening chart, restricted so that its zero-normal locus is exactly
the actual embedded support on its entire source. Every ingredient has been constructed
from the given smooth closed immersion. -/
def closedImmersionFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X)
      ((Fin m → ℂ) ×
        (closedImmersionDerivativeProjection X Y i m d z).ker) :=
  ((localChart X d (Point.map i z)).trans
    (closedImmersionNormalChart X Y i m d z).symm).restrOpen
      (exists_open_normalCriterion X Y i m d z).choose
      (exists_open_normalCriterion X Y i m d z).choose_spec.1

@[simp] theorem closedImmersionFlatteningChart_apply (y : ComplexPoint X) :
    closedImmersionFlatteningChart X Y i m d z y =
      (closedImmersionNormalChart X Y i m d z).symm
        (localChart X d (Point.map i z) y) := rfl

theorem closedImmersionFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionFlatteningChart X Y i m d z).source :=
  ⟨⟨mem_localChart_source X d (Point.map i z),
      closedImmersionNormalChart_mem_target X Y i m d z⟩,
    (exists_open_normalCriterion X Y i m d z).choose_spec.2.1⟩

@[simp] theorem closedImmersionFlatteningChart_center :
    closedImmersionFlatteningChart X Y i m d z (Point.map i z) =
      (localChart Y m z z, 0) :=
  closedImmersionNormalChart_symm_center X Y i m d z

/-- The complete geometric support is flattened, not merely a parametrized sub-piece. -/
theorem closedImmersionFlatteningChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (Point.map i) ↔
      (closedImmersionFlatteningChart X Y i m d z y).2 = 0 :=
  (exists_open_normalCriterion X Y i m d z).choose_spec.2.2 y hy.2

/-- Identifying the actual normal space with standard complex coordinates uses only its
proved complex dimension. This is a complex-linear coordinate choice, not a choice of
homology generator or an orientation class. -/
def closedImmersionNormalKernelEquiv :
    (closedImmersionDerivativeProjection X Y i m d z).ker ≃L[ℂ]
      (Fin (d - m) → ℂ) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      closedImmersionNormalKernel_finrank X Y i m d z)).toContinuousLinearEquiv

/-- The actual ambient support-flattening chart in standard tangent and normal complex
spaces, ready for the normal-slice pair calculation. -/
def closedImmersionStandardFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (closedImmersionFlatteningChart X Y i m d z).trans
    (((ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
      (closedImmersionNormalKernelEquiv X Y i m d z)).toHomeomorph.toOpenPartialHomeomorph)

@[simp] theorem closedImmersionStandardFlatteningChart_apply (y : ComplexPoint X) :
    closedImmersionStandardFlatteningChart X Y i m d z y =
      ((closedImmersionFlatteningChart X Y i m d z y).1,
        closedImmersionNormalKernelEquiv X Y i m d z
          (closedImmersionFlatteningChart X Y i m d z y).2) := rfl

@[simp] theorem closedImmersionStandardFlatteningChart_source :
    (closedImmersionStandardFlatteningChart X Y i m d z).source =
      (closedImmersionFlatteningChart X Y i m d z).source := by
  simp only [closedImmersionStandardFlatteningChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

theorem closedImmersionStandardFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionStandardFlatteningChart X Y i m d z).source := by
  rw [closedImmersionStandardFlatteningChart_source]
  exact closedImmersionFlatteningChart_mem_source X Y i m d z

@[simp] theorem closedImmersionStandardFlatteningChart_center :
    closedImmersionStandardFlatteningChart X Y i m d z
      (Point.map i z) = (localChart Y m z z, 0) := by
  simp only [closedImmersionStandardFlatteningChart_apply, closedImmersionFlatteningChart_center,
    map_zero]

/-- The support is exactly the zero-normal plane throughout the actual chart source. -/
theorem closedImmersionStandardFlatteningChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionStandardFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (Point.map i) ↔
      (closedImmersionStandardFlatteningChart X Y i m d z y).2 = 0 := by
  rw [closedImmersionStandardFlatteningChart_source] at hy
  simpa only [closedImmersionStandardFlatteningChart_apply, ContinuousLinearEquiv.map_eq_zero_iff] using
    closedImmersionFlatteningChart_mem_range_iff X Y i m d z y hy

end AlgebraicGeometry.ComplexPoint
