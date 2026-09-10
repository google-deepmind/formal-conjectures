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

public import FormalConjecturesForMathlib.AlgebraicGeometry.HodgeFiltration
public import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexSingularComparison

/-!
# Betti and constant-sheaf comparison

On the analytic space of a smooth complex scheme, the rational constant sheaf is resolved by
the sheafified rational singular-cochain complex. Localizing at quasi-isomorphisms gives a
canonical comparison equivalence in every cohomological degree.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def rationalToSingularCochainComplexInt :
    constantFieldSheafComplexInt ℚ X ⟶
      singularCochainSheafComplexInt X ℚ :=
  constantsToSingularCochainComplexInt X ℚ

/-- The rational constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma rationalToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (rationalToSingularCochainComplexInt X) := by
  change QuasiIso (constantsToSingularCochainComplexInt X ℚ)
  exact constantsToSingularCochainComplexInt_quasiIso X ℚ

/-- Hypercohomology of the integer-indexed rational singular-cochain sheaf complex. -/
abbrev RationalSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  Hypercohomology X (singularCochainSheafComplexInt X ℚ) n

/-- Rational constant-sheaf cohomology is canonically equivalent to the hypercohomology of its
singular-cochain resolution. -/
def rationalCohomologySingularCochainEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FieldCohomology ℚ X n ≃
      RationalSingularCochainHypercohomology X n :=
  Localization.SmallShiftedHom.postcompEquiv
    (rationalToSingularCochainComplexInt X)
    (rationalToSingularCochainComplexInt_quasiIso X)

/-- The comparison equivalence is the map on hypercohomology induced by the canonical
constant-to-singular-cochain morphism. -/
lemma rationalCohomologySingularCochainEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FieldCohomology ℚ X n) :
    rationalCohomologySingularCochainEquiv X n α =
      hypercohomologyMap X
        (rationalToSingularCochainComplexInt X) n α :=
  rfl

/-- The rational constant-to-singular comparison is additive. -/
def rationalCohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    FieldCohomology ℚ X n ≃+
      RationalSingularCochainHypercohomology X n where
  toEquiv := rationalCohomologySingularCochainEquiv X n
  map_add' α β :=
    (hypercohomologyMap X
      (rationalToSingularCochainComplexInt X) n).map_add α β

@[simp]
lemma rationalCohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : FieldCohomology ℚ X n) :
    rationalCohomologySingularCochainAddEquiv X n α =
      hypercohomologyMap X
        (rationalToSingularCochainComplexInt X) n α :=
  rfl

end AlgebraicGeometry.ComplexPoint
