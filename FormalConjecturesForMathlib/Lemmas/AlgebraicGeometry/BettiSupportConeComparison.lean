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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiSupportSingularNaturality

import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiSupportSingularComparison

/-!
# Betti support-cone comparison

The natural singular-cochain restriction strictly extends restriction of rational constants.
Consequently, replacement of the constant source by its natural singular resolution induces a
quasi-isomorphism between the associated support cones.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))

local instance bettiSupportConeComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction through the natural singular resolution agrees strictly with restriction of
rational constants before extending the complexes to integer degrees. -/
lemma rationalToSingular_comp_naturalSingularResolutionRestrictionNat
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    constantsToSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X)) ≫
        naturalSingularResolutionRestrictionNat X Z hZ =
      rationalRestrictionComplexNat X Z := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      dsimp only [naturalSingularResolutionRestrictionNat]
      rw [HomologicalComplex.comp_f]
      unfold rationalRestrictionComplexNat
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
      rw [show (constantsToSingularCochainSheafComplex ℚ
          (TopCat.of (ComplexPoint X))).f 0 =
            constantsToSingularCochainZeroSheaf ℚ
              (TopCat.of (ComplexPoint X)) from rfl]
      change constantsToSingularCochainZeroSheaf ℚ
            (TopCat.of (ComplexPoint X)) ≫
          singularRestrictionSheaf ℚ
              (analyticComplementInclusion X Z) 0 ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat
              (analyticComplementInclusion X Z)).map
                ((complementSingularToInjectiveResolution X Z hZ).f 0)) = _
      rw [← Category.assoc,
        constantsToSingularCochainZeroSheaf_comp_singularRestriction X Z,
        Category.assoc, ← Functor.map_comp]
      have hcomp := HomologicalComplex.congr_hom
        (complementConstants_comp_singularToInjectiveResolution
          X Z hZ) 0
      change constantsToSingularCochainZeroSheaf ℚ
          (TopCat.of (AnalyticComplement X Z)) ≫
            (complementSingularToInjectiveResolution X Z hZ).f 0 =
          (complementConstantRationalInjectiveResolution X Z).ι.f 0 at hcomp
      rw [hcomp]
      rfl
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (constantFieldSheaf ℚ X) (n + 1) (by lia)).eq_of_src _ _

/-- Restriction through the integer-indexed natural singular resolution agrees strictly with
restriction of rational constants. -/
lemma rationalToSingular_comp_naturalSingularResolutionRestriction
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalToSingularCochainComplexInt X ≫
        naturalSingularResolutionRestriction X Z hZ =
      rationalRestrictionComplexInt X Z := by
  unfold rationalToSingularCochainComplexInt constantsToSingularCochainComplexInt
    naturalSingularResolutionRestriction rationalRestrictionComplexInt
  calc
    _ = HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex ℚ
            (TopCat.of (ComplexPoint X)) ≫
          naturalSingularResolutionRestrictionNat X Z hZ)
        ComplexShape.embeddingUpNat :=
      (HomologicalComplex.extendMap_comp _ _ ComplexShape.embeddingUpNat).symm
    _ = _ := congrArg
      (fun f ↦ HomologicalComplex.extendMap f ComplexShape.embeddingUpNat)
      (rationalToSingular_comp_naturalSingularResolutionRestrictionNat
        X Z hZ)

/-- Replacing rational constants by the natural singular-cochain resolution induces a map of
support cones. -/
def rationalSupportConeToNaturalSingularCone
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplex X Z ⟶
      CochainComplex.mappingCone
        (naturalSingularResolutionRestriction X Z hZ) :=
  CochainComplex.mappingCone.map
    (rationalRestrictionComplexInt X Z)
    (naturalSingularResolutionRestriction X Z hZ)
    (rationalToSingularCochainComplexInt X) (𝟙 _)
    (by rw [Category.comp_id,
      rationalToSingular_comp_naturalSingularResolutionRestriction X Z hZ])

/-- The natural singular-resolution replacement map between support cones is a
quasi-isomorphism. -/
noncomputable instance rationalSupportConeToNaturalSingularCone_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToNaturalSingularCone X Z hZ) := by
  let : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  change QuasiIso (CochainComplex.mappingCone.map
    (rationalRestrictionComplexInt X Z)
    (naturalSingularResolutionRestriction X Z hZ)
    (rationalToSingularCochainComplexInt X) (𝟙 _)
    (by rw [Category.comp_id,
      rationalToSingular_comp_naturalSingularResolutionRestriction X Z hZ]))
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso
    (rationalRestrictionComplexInt X Z)
    (naturalSingularResolutionRestriction X Z hZ)
    (rationalToSingularCochainComplexInt X) (𝟙 _) _

end AlgebraicGeometry.ComplexPoint
