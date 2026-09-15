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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ClosedImmersionNormalCoordinates

/-!
# Constructed normal coordinates for smooth closed immersions

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ClosedImmersionNormalCoordinates`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology Filter

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint Y)

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

theorem closedImmersionFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionFlatteningChart X Y i m d z).source :=
  ⟨⟨mem_localChart_source X d (Point.map i z),
      closedImmersionNormalChart_mem_target X Y i m d z⟩,
    (exists_open_normalCriterion X Y i m d z).choose_spec.2.1⟩

/-- The complete geometric support is flattened, not merely a parametrized sub-piece. -/
theorem closedImmersionFlatteningChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (Point.map i) ↔
      (closedImmersionFlatteningChart X Y i m d z y).2 = 0 :=
  (exists_open_normalCriterion X Y i m d z).choose_spec.2.2 y hy.2

theorem closedImmersionStandardFlatteningChart_mem_source :
    Point.map i z ∈
      (closedImmersionStandardFlatteningChart X Y i m d z).source := by
  rw [closedImmersionStandardFlatteningChart_source]
  exact closedImmersionFlatteningChart_mem_source X Y i m d z

/-- The support is exactly the zero-normal plane throughout the actual chart source. -/
theorem closedImmersionStandardFlatteningChart_mem_range_iff (y : ComplexPoint X)
    (hy : y ∈ (closedImmersionStandardFlatteningChart X Y i m d z).source) :
    y ∈ Set.range (Point.map i) ↔
      (closedImmersionStandardFlatteningChart X Y i m d z y).2 = 0 := by
  rw [closedImmersionStandardFlatteningChart_source] at hy
  simpa only [closedImmersionStandardFlatteningChart_apply, ContinuousLinearEquiv.map_eq_zero_iff] using
    closedImmersionFlatteningChart_mem_range_iff X Y i m d z y hy

end AlgebraicGeometry.ComplexPoint
