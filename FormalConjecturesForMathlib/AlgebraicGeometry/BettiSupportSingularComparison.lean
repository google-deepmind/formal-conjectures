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

public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiSupportSingularNaturality

/-!
# Singular cochains and Betti cohomology with support

This file proves that the degree-zero inclusion of rational constants into singular cochains
commutes with restriction to an analytic complement. This is the strict naturality square
needed before comparing the associated mapping cones.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The chain map on a preimage open commutes with the zero-chain augmentation. -/
lemma preimageOpenChainMap_comp_zeroAugmentation
    (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X) (V : Opens X) :
    (preimageOpenChainMap R j V).f 0 ≫
        openZeroAugmentation R X (.op V) =
      openZeroAugmentation R U (.op ((Opens.map j).obj V)) := by
  change (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map (preimageOpenToOpen j V)).f 0 ≫
        openZeroAugmentation R X (.op V) =
      openZeroAugmentation R U (.op ((Opens.map j).obj V))
  exact simplicialZeroAugmentation_naturality R
    (TopCat.toSSet.map (preimageOpenToOpen j V))

set_option backward.isDefEq.respectTransparency false in
/-- Raw restriction carries a constant singular zero-cochain to the same constant cochain. -/
lemma constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward
    (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X) :
    constantsToSingularCochainZero R X ≫
        singularRestrictionToRawPushforward R j 0 =
      Functor.whiskerLeft (Opens.map j).op
        (constantsToSingularCochainZero R U) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro r
  change R at r
  change ((preimageOpenChainMap R j V.unop).f 0).hom.dualMap
      (constantSingularZeroCochain R X V r) =
    constantSingularZeroCochain R U
      (.op ((Opens.map j).obj V.unop)) r
  apply LinearMap.ext
  intro c
  simp only [LinearMap.dualMap_apply]
  change (r • (openZeroAugmentation R X V).hom)
      (((preimageOpenChainMap R j V.unop).f 0).hom c) =
    (r • (openZeroAugmentation R U
      (.op ((Opens.map j).obj V.unop))).hom) c
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  exact congrArg (r • ·) (ConcreteCategory.congr_hom
    (preimageOpenChainMap_comp_zeroAugmentation R j V.unop) c)

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ))

set_option backward.isDefEq.respectTransparency false in
/-- Constant singular zero-cochains commute with restriction to an analytic complement. -/
lemma constantsToSingularCochainZeroSheaf_comp_singularRestriction
    (Z : Set (ComplexPoint X)) :
    constantsToSingularCochainZeroSheaf ℚ
          (TopCat.of (ComplexPoint X)) ≫
        singularRestrictionSheaf ℚ
          (analyticComplementInclusion X Z) 0 =
      rationalRestrictionSheaf X Z ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat
          (analyticComplementInclusion X Z)).map
            (constantsToSingularCochainZeroSheaf ℚ
              (TopCat.of (AnalyticComplement X Z))) := by
  apply Sheaf.hom_ext
  change sheafifyMap (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X)))
        (constantsToSingularCochainZero ℚ
          (TopCat.of (ComplexPoint X))) ≫
      (singularRestrictionSheaf ℚ
        (analyticComplementInclusion X Z) 0).hom =
    (rationalRestrictionSheaf X Z).hom ≫
      Functor.whiskerLeft
        (Opens.map (analyticComplementInclusion X Z)).op
        (sheafifyMap (Opens.grothendieckTopology
          (TopCat.of (AnalyticComplement X Z)))
          (constantsToSingularCochainZero ℚ
            (TopCat.of (AnalyticComplement X Z))))
  apply sheafify_hom_ext
    (J := Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X)))
    (P := constantCoefficientPresheaf ℚ
      (TopCat.of (ComplexPoint X))) _ _
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).obj
        (singularCochainSheaf ℚ
          (TopCat.of (AnalyticComplement X Z)) 0)).property
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    toSheafify_comp_singularRestrictionSheaf]
  unfold rationalRestrictionSheaf
  rw [← Category.assoc, toSheafify_sheafifyLift]
  unfold singularRestrictionPresheaf rationalRestrictionPresheaf
  rw [← Functor.whiskerLeft_comp]
  change _ = Functor.whiskerLeft
    (Opens.map (analyticComplementInclusion X Z)).op
      (toSheafify (Opens.grothendieckTopology
          (TopCat.of (AnalyticComplement X Z)))
          (constantCoefficientPresheaf ℚ
            (TopCat.of (AnalyticComplement X Z))) ≫
        sheafifyMap (Opens.grothendieckTopology
          (TopCat.of (AnalyticComplement X Z)))
          (constantsToSingularCochainZero ℚ
            (TopCat.of (AnalyticComplement X Z))))
  have hunit := toSheafify_naturality
    (Opens.grothendieckTopology
      (TopCat.of (AnalyticComplement X Z)))
    (constantsToSingularCochainZero ℚ
      (TopCat.of (AnalyticComplement X Z)))
  rw [← hunit, Functor.whiskerLeft_comp, ← Category.assoc,
    constantsToSingularCochainZero_comp_singularRestrictionToRawPushforward]

end AlgebraicGeometry.ComplexPoint
