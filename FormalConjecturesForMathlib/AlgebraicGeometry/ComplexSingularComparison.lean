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

public import FormalConjecturesForMathlib.AlgebraicGeometry.Points
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainSheaf
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import FormalConjecturesForMathlib.AlgebraicGeometry.ComplexManifold
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Singular cochains on smooth complex-point spaces

The algebraic coordinate charts on a smooth complex scheme give a basis of open contractible
neighborhoods. Singular chains on each such neighborhood are exact in positive degree. Duality
therefore supplies local primitives for singular cochains. Together with the explicit degree-zero
calculation, this proves that the constant-sheaf-to-singular-cochain map is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The constant-to-singular-cochain comparison on a smooth complex-point space is a
quasi-isomorphism in positive degrees. -/
lemma constantsToSingularCochain_quasiIsoAt_succ
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [Field R] (n : ℕ) :
    QuasiIsoAt
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint X))) (n + 1) := by
  apply AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_contractibleOpenBasis
  exact fun x U hxU ↦ exists_contractibleOpen_le X x U hxU

/-- The constant-to-singular-cochain comparison on a smooth complex-point space is a
quasi-isomorphism in degree zero. -/
lemma constantsToSingularCochain_quasiIsoAt_zero
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [Field R] :
    QuasiIsoAt
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint X))) 0 := by
  let : LocallyPathConnectedSpace (ComplexPoint X) :=
    locallyPathConnectedSpace X
  exact
    AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex_quasiIsoAt_zero
      R (TopCat.of (ComplexPoint X))

/-- On the analytic space of a smooth complex scheme, the constant sheaf is resolved by the
sheafified singular-cochain complex. -/
lemma constantsToSingularCochain_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [Field R] :
    QuasiIso
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint X))) := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero => exact constantsToSingularCochain_quasiIsoAt_zero X R
  | succ n => exact constantsToSingularCochain_quasiIsoAt_succ X R n

/-- The sheafified singular-cochain complex, extended by zero to integer degrees. -/
def singularCochainSheafComplexInt (R : Type) [Field R] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  (AlgebraicTopology.Singular.singularCochainSheafComplex R
    (TopCat.of (ComplexPoint X))).extend ComplexShape.embeddingUpNat

/-- The constant coefficient sheaf complex, extended by zero to integer degrees. -/
def constantCoefficientSheafComplexInt (R : Type) [Field R] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)))).obj
      (AlgebraicTopology.Singular.constantCoefficientSheaf R
        (TopCat.of (ComplexPoint X)))).extend ComplexShape.embeddingUpNat

/-- The constant-to-singular comparison, extended by zero to integer degrees. -/
def constantsToSingularCochainComplexInt (R : Type) [Field R] :
    constantCoefficientSheafComplexInt X R ⟶
      singularCochainSheafComplexInt X R :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat

/-- The integer-indexed constant-to-singular comparison remains a quasi-isomorphism. -/
lemma constantsToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [Field R] :
    QuasiIso (constantsToSingularCochainComplexInt X R) := by
  unfold constantsToSingularCochainComplexInt constantCoefficientSheafComplexInt
    singularCochainSheafComplexInt
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat).mpr
        (constantsToSingularCochain_quasiIso X R)

end AlgebraicGeometry.ComplexPoint
