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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleClass
/-!
# The coniveau subspace

For a projective complex variety, a class supported on a closed set `Z` belongs to the homotopy
fiber of `RΓ(X, ℚ) → RΓ(X ∖ Z, ℚ)`, and its image in ordinary cohomology is the canonical
connecting map. The sum of these images over codimension-`p` algebraic subsets is the coniveau
subspace.

It is only an upper bound for the span of cycle classes until cohomological purity has been
proved: an arbitrary supported cohomology class is not, by definition, a fundamental class. The
construction is therefore kept explicitly named as such, alongside an intrinsic component line
defined from generators of the entire supported image, for stating comparison theorems. The
algebraic cycle-class span itself is defined from the actual normalized component classes of
`CycleComponentSheafClass`, and the two agree once purity holds.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- Rational constant-sheaf cohomology supported on a closed subset of an analytification. -/
abbrev RationalConstantSheafCohomologyWithSupport
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :=
  RationalCohomologyWithSupport X Z n

/-- The rational span in ordinary cohomology of classes supported on `Z`. -/
def rationalCohomologySupportedOn
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :
    Submodule ℚ (H^n(X; ℚ)) :=
  Submodule.span ℚ (Set.range (forgetSupport X Z n))

/-- A class which generates the whole degree-`2p` image of cohomology supported on one
irreducible component. This is a property inside ordinary rational cohomology; it does not assume
that the supported image is one-dimensional. Cohomological purity proves that such a generator
is precisely a nonzero rational multiple of the component's fundamental class. -/
def IsRationalComponentCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (x : X.left) (α : H^(2 * (p : ℤ))(X; ℚ)) : Prop :=
  α ∈ rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ)) ∧
    Submodule.span ℚ {α} =
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ))

/-- The intrinsic cycle-class line of an irreducible codimension-`p` component. Taking the span
of all generators removes the arbitrary choice of generator and its rational scaling. -/
def rationalComponentCycleClassLine
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) :
    Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  Submodule.span ℚ {α | IsRationalComponentCycleClass X p x α}

/-- Cohomological purity for a component, stated independently of the construction of any
particular supported class: its fundamental-class line is the whole supported image in the
critical degree. -/
def RationalComponentCycleClassPurity
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) : Prop :=
  rationalComponentCycleClassLine X p x =
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

/-- The rational span of the actually constructed codimension-`p` component classes.

The relative dimension is the canonical `dim X`, whose certificate is proved from smoothness and
integrality. This definition spans explicit class terms; it does not quantify over hypothetical
generators and does not assume descent to the Chow group. -/
def algebraicCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx}

/-- The degree-`2p` rational coniveau subspace obtained from all cohomology classes supported on
irreducible algebraic subvarieties of codimension `p`. This is not the cycle-class span unless a
purity theorem identifying each relevant image with its fundamental-class line is supplied. -/
def rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (_ : coheight x = p),
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

end AlgebraicGeometry.ComplexPoint
