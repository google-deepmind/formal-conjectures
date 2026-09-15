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

public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiCohomologyWithSupportComparison

/-!
# Betti comparison with support

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiCohomologyWithSupportComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

end Topology.IsOpenEmbedding

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

end

end CochainComplex

namespace AlgebraicTopology.Singular

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

variable [IsIntegral X.left] [Smooth X.hom]

attribute [local instance] bettiSupportComparisonHasDerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- The singular-resolution restriction strictly extends restriction of rational constants. -/
lemma rationalToSingular_comp_singularResolutionRestriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalToSingularCochainComplexInt X ≫
        singularResolutionRestriction X Z hZ =
      rationalRestrictionComplexInt X Z := by
  let : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
    unfold constantFieldSheafComplexInt
    infer_instance
  let : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
    unfold singularCochainSheafComplexInt
    infer_instance
  let : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE
      0 := by
    unfold derivedPushforwardComplementConstantRationalComplexInt
    infer_instance
  let : Mono (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_mono X
  let : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  exact CochainComplex.comp_liftToInjective
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

end AlgebraicGeometry.ComplexPoint
