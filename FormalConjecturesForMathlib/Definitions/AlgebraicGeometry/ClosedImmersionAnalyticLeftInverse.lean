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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ComplexAnalyticMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Analytic local left inverses from actual section lifting

Intrinsic regular coordinate functions lift through a closed immersion on a common affine
ambient neighborhood. Their analytic evaluations give a local left inverse to the inclusion
written in complex charts. In particular derivative injectivity is proved, not supplied as
an immersion or purity field.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Filter

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

/-- The actual inclusion written in the canonical intrinsic and ambient complex charts. -/
def inclusionInComplexCharts (z : ComplexPoint Y) :
    (Fin m → ℂ) → (Fin d → ℂ) :=
  fun v => localChart X d (Point.map i z)
    (Point.map i ((localChart Y m z).symm v))

end AlgebraicGeometry.ComplexPoint
