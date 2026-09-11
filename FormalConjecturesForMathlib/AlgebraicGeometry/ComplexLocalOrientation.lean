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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
public import FormalConjecturesForMathlib.AlgebraicTopology.ChartLocalFundamentalClassGenerator

/-!
# Local homology orientation of a smooth complex scheme

The algebraic étale charts of a smooth complex scheme construct, at every complex point, an
exactly normalized class in top local homology.  The normalization is the standard complex
orientation: real and imaginary coordinate directions are interleaved in that order.

This file packages the pointwise construction as a family.  It does not assume a generator or
choose a nonzero rational multiple: the generator theorem follows from point-neighborhood
excision and the explicit standard complex fundamental class.

Compatibility of these classes on overlaps is a separate naturality theorem.  At the
differential level, complex-linear coordinate changes preserve the orientation by
`Orientation.map_restrictScalars_complexLinearEquiv`; the remaining bridge is invariance of the
explicit local homology class under orientation-preserving chart changes.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The canonical pointwise local orientation of a smooth complex scheme, constructed from its
algebraic étale charts and the standard complex local class. -/
def complexLocalOrientation [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) : RelativeHomology ℚ (pointComplementPair z) (2 * d) :=
  localClassOfChart d (localChart X d z) z (mem_localChart_source X d z)

/-- The local orientation is exactly the standard complex class transported through the
canonical algebraic étale chart at the point. -/
lemma complexLocalOrientation_eq_localClassOfChart
    [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) :
    complexLocalOrientation X d z =
      localClassOfChart d (localChart X d z) z
        (mem_localChart_source X d z) :=
  rfl

/-- At every point of a `T₁` smooth complex analytic space, the constructed local orientation
class generates the full top local homology group. -/
theorem span_complexLocalOrientation_eq_top
    [SmoothOfRelativeDimension d X.hom]
    [T1Space (ComplexPoint X)]
    (z : ComplexPoint X) :
    Submodule.span ℚ {complexLocalOrientation X d z} = ⊤ := by
  rw [complexLocalOrientation_eq_localClassOfChart]
  exact span_localClassOfChart_eq_top d (localChart X d z) z
    (mem_localChart_source X d z)

end AlgebraicGeometry.ComplexPoint
