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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.NormalProjectionOverlap

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

variable (z' : ComplexPoint Y)

end AlgebraicGeometry.ComplexPoint
