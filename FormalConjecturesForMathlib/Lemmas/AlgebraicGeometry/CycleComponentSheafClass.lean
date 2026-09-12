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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSheafClass

/-!
# Constructed sheaf cycle classes in arbitrary codimension

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.CycleComponentSheafClass`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] cycleComponentSheafClassAnalyticTopology

variable (x : X.left) {d p : ℕ} [SmoothOfRelativeDimension d X.hom]
  (hx : Order.coheight x = p)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).hom
      (cycleComponentSupportedInjectiveClass X x (d := d) hx) =
    cycleComponentSmoothSupportCoclassSection X x (d := d) hx :=
  (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).addCommGroupIsoToAddEquiv.apply_symm_apply _

/-- The normalized global extension is unique, by injectivity of the actual
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ)))
    (ha : (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).hom a =
      cycleComponentSmoothSupportCoclassSection X x (d := d) hx) :
    a = cycleComponentSupportedInjectiveClass X x (d := d) hx :=
  (cycleComponentSupportedClassNormalizationIso X x (d := d) hx).addCommGroupIsoToAddEquiv.injective
    (ha.trans (cycleComponentSupportedInjectiveClass_normalization X x (d := d) hx).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary class agrees with the repository's support-forgetting map,
through the constructed, sign-correct support comparison. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass X x (d := d) hx =
      forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
        (cycleComponentSheafSupportedClass X x (d := d) hx) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).injective
  rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    (cycleComponentSupport X x) (cycleComponentAnalyticClosedSupport X x).isClosed]
  simp only [cycleComponentSheafClass, cycleComponentSheafSupportedClass,
    AddEquiv.apply_symm_apply]
  rfl

/-- The constructed Alexander–Poincaré map sends the fundamental class to
the exact normalized supported class, with no comparison hypothesis. -/
@[simp]
theorem cycleComponentSheafBorelMooreFundamentalClass_duality :
    complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafSupportedClass X x (d := d) hx :=
  AddEquiv.apply_symm_apply _ _

/-- The ordinary class is also exactly the actual ambient Borel–Moore
cycle-class route. The ordinary-target comparison is proved, not an input. -/
theorem cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology :
    complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx) =
    cycleComponentSheafClass X x (d := d) hx := by
  change forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport X d
      (cycleComponentAnalyticClosedSupport X x) p
      (cycleComponentSheafClass_codimension_le X x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass X x (d := d) hx)) = _
  rw [cycleComponentSheafBorelMooreFundamentalClass_duality,
    cycleComponentSheafClass_eq_forgetSupport]

end AlgebraicGeometry.ComplexPoint
