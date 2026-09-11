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

public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexSheafBorelMooreForget
public import FormalConjecturesForMathlib.AlgebraicGeometry.DerivedSupportRationalForget

/-!
# The constructed ambient Borel–Moore map into the existing rational cohomology API

The comparison is the actual complex-orientation duality followed by the constructed
injective-resolution/support-cone equivalence. Forgetting support then lands in the
repository's `H^n(X; ℚ)` itself, with no supplied duality or comparison argument.

This module transports Borel–Moore classes; it does not produce fundamental classes
for general algebraic components. Agreement with the actual derived-global
support-forgetting route is proved below, using the normalized support-cone
comparison including its sign. Agreement with the existing point coclass for a
particular fundamental-class construction remains a separate comparison theorem.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

local instance complexBorelMooreRationalComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The actual derived-support groups agree with the existing rational support API,
through its constructed resolution and cone comparison. -/
def complexDerivedSupportedCohomologyAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X)) (n : ℤ) :
    ComplexDerivedSupportedCohomology X Z n ≃+
      RationalCohomologyWithSupport X Z n :=
  derivedRationalSupportAddEquiv X Z n

variable [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]

/-- The smooth-ambient Borel–Moore comparison with the existing rational support
cohomology, derived from geometric orientation and actual supported resolutions. -/
def complexAmbientSheafBorelMooreAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology X d Z i ≃+
      RationalCohomologyWithSupport X Z (2 * (d : ℤ) - i) :=
  (complexAmbientSheafBorelMooreHomologyIso X d Z i).addCommGroupIsoToAddEquiv.trans
    (complexDerivedSupportedCohomologyAddEquivRationalSupport X Z (2 * (d : ℤ) - i))

/-- The cycle-degree comparison lands in degree `2p` using the proved shift arithmetic. -/
def complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
    (Z : Closeds (ComplexPoint X)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology X d Z
        (2 * ((d - p : ℕ) : ℤ)) ≃+
      RationalCohomologyWithSupport X Z (2 * (p : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeIso X d Z p hp).addCommGroupIsoToAddEquiv.trans
    (complexDerivedSupportedCohomologyAddEquivRationalSupport X Z (2 * (p : ℤ)))

/-- An explicit additive map from actual ambient Borel–Moore homology to the
repository's ordinary rational cohomology. It requires a class, not a duality datum. -/
def complexAmbientSheafBorelMooreToFieldCohomology
    (Z : Closeds (ComplexPoint X)) (i : ℤ) :
    ComplexAmbientSheafBorelMooreHomology X d Z i →+
      H^(2 * (d : ℤ) - i)(X; ℚ) :=
  (forgetSupport X (Z : Set (ComplexPoint X))
    (2 * (d : ℤ) - i)).comp
      (complexAmbientSheafBorelMooreAddEquivRationalSupport X d Z i).toAddMonoidHom

/-- Cycle-degree transport into the existing ordinary cohomology API. No global
component class or local-purity theorem is silently supplied by this map. -/
def complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology
    (Z : Closeds (ComplexPoint X)) (p : ℕ) (hp : p ≤ d) :
    ComplexAmbientSheafBorelMooreHomology X d Z
        (2 * ((d - p : ℕ) : ℤ)) →+
      H^(2 * (p : ℤ))(X; ℚ) :=
  (forgetSupport X (Z : Set (ComplexPoint X))
    (2 * (p : ℤ))).comp
      (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport
        X d Z p hp).toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The existing-cohomology adapter is exactly the actual derived support-forgetting
map transported through the constructed ordinary cohomology comparison. In
particular no independent sign or scalar is chosen at the final adapter. -/
theorem complexAmbientSheafBorelMooreToFieldCohomology_eq_derivedForget
    (Z : Closeds (ComplexPoint X)) (i : ℤ)
    (x : ComplexAmbientSheafBorelMooreHomology X d Z i) :
    complexAmbientSheafBorelMooreToFieldCohomology X d Z i x =
      derivedRationalCohomologyAddEquiv X (2 * (d : ℤ) - i)
        (complexAmbientSheafBorelMooreToCohomology X d Z i x) :=
  (derivedRationalSupportAddEquiv_forgetSupport X Z (2 * (d : ℤ) - i)
    ((complexAmbientSheafBorelMooreHomologyIso X d Z i).hom x)).symm

end AlgebraicGeometry.ComplexPoint
