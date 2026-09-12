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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.AlgebraicCycleSupport
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.ChowGroupLift
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CohomologyWithSupport
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CycleComponentSheafClass
/-!
# The cycle class in codimension zero

For an integral projective complex variety, the class of a codimension-zero cycle in rational
Betti cohomology is a multiple of the unit class, and the multiple is the coefficient the cycle
gives to the generic point. This identifies the genuine Chow-group cycle-class map in
codimension zero, which needs no purity input.

In positive codimension a map on Chow groups additionally requires Gysin compatibility and
vanishing on rational equivalences; neither fact is postulated here. The Hodge conjecture itself
only needs the span of the classes of irreducible subvarieties, so it does not require choosing
such a Chow-group map.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The rational Chow class represented by an irreducible codimension-`p` component with
coefficient one. -/
def rationalComponentChowClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (x : X.left) (hx : coheight x = p) : RationalChowGroup X.left p :=
  ChowGroup.toRational (ChowGroup.mk (CodimensionCycle.single x hx 1))

/-! ### The genuine codimension-zero cycle class -/

/-- A codimension-zero cycle maps to the constant cohomology class given by the coefficient of
the generic component. -/
def codimensionZeroCycleClassOnCycles
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    CodimensionCycle X.left 0 →+ H^0(X; ℚ) :=
  (fieldCohomologyClassAddHom ℚ X).comp
    ((Int.castAddHom ℚ).comp CodimensionCycle.integralEquiv.toAddMonoidHom)

/-- Codimension-zero rational equivalences map to zero. Here this is a theorem rather than part
of the data of the cycle-class map: the rational-equivalence subgroup is trivial in codimension
zero. -/
lemma rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalEquivalenceSubgroup X.left 0 ≤
      (codimensionZeroCycleClassOnCycles X).ker := by
  rw [rationalEquivalenceSubgroup_zero]
  exact bot_le

/-- The genuine integral codimension-zero cycle-class map on the Chow group. -/
def codimensionZeroChowCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ChowGroup X.left 0 →+ H^0(X; ℚ) :=
  ChowGroup.liftCycleClass (codimensionZeroCycleClassOnCycles X)
    (rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker X)

/-- The rational codimension-zero Chow group of an integral variety maps to degree-zero
cohomology by rational extension of the integral class map. -/
def codimensionZeroCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    RationalChowGroup X.left 0 →ₗ[ℚ] H^0(X; ℚ) :=
  ChowGroup.rationalExtension (codimensionZeroChowCycleClass X)

/-- The actual codimension-zero algebraic cycle-class span. -/
def codimensionZeroCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Submodule ℚ (H^0(X; ℚ)) :=
  LinearMap.range (codimensionZeroCycleClass X)

end AlgebraicGeometry.ComplexPoint
