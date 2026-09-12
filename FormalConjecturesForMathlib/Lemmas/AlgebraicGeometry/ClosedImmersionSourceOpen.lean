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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ClosedImmersionSourceOpen

/-!
# Restricting the source of a closed immersion without losing closedness

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.ClosedImmersionSourceOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme} (i : Y ⟶ X) [IsClosedImmersion i] (A : Y.Opens)

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

/-- The actual immersion image formula, with structure-map compatibility bundled in `i`. -/
theorem range_map_of_isImmersion_of_comm (X Y : Over (Spec (.of ℂ)))
    (i : Y ⟶ X) [IsImmersion i.left] [LocallyOfFiniteType X.hom] :
    Set.range (Point.map i) =
      (Point.underlying : ComplexPoint X → X.left) ⁻¹' Set.range i.left := by
  let : LocallyOfFiniteType Y.hom := by
    rw [← i.w]
    infer_instance
  exact range_map_of_isImmersion X i

end AlgebraicGeometry.ComplexPoint
