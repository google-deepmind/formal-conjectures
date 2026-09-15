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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSupportExtension

/-!
# Actual unique extension across a cycle component's singular boundary

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSupportExtension`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {d p : ℕ} [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p)

attribute [local instance] cycleComponentSupportExtensionAnalyticTopology

@[simp]
theorem cycleComponentSupportExtensionIso_hom :
    (cycleComponentSupportExtensionIso X x (d := d) hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x) (2 * (p : ℤ)) := rfl

end AlgebraicGeometry.ComplexPoint
