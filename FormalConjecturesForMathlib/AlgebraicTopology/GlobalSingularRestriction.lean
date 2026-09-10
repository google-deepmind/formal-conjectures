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
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularSubdivisionCochainSheaf

/-!
# Global singular restriction

This file identifies the top-open comparison with the chosen sheafification unit and proves
that global singular restriction commutes strictly with that unit. This is the naturality square
needed to compare a support cone built from singular-cochain sheaves with the corresponding raw
singular-cochain cone.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] {U X : TopCat.{0}} (j : U ⟶ X)

/-- Restriction of the raw singular-cochain presheaf complexes. -/
def singularRawRestrictionComplex :
    singularCochainPresheafComplex R X ⟶
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ) |>.obj (singularCochainPresheafComplex R U) where
  f n := singularRestrictionToRawPushforward R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [singularCochainPresheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      singularCochainPresheafComplex_d]
    exact (singularRestrictionToRawPushforward_coboundary R j i).symm

/-- Raw singular cochains on the inverse image of the top open. -/
def globalRawPushforwardSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op (⊤ : Opens X))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex R U)))

/-- Global sections of the pushforward singular-cochain sheaf complex. -/
def globalPushforwardSingularCochainSheafComplex : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (singularCochainSheafComplex R U)))

/-- Restriction of raw global singular cochains to the inverse image of the top open. -/
def globalRawSingularRestriction :
    globalRawSingularCochainComplex R X ⟶
      globalRawPushforwardSingularCochainComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularRawRestrictionComplex R j)

/-- Restriction on the global-section complexes of singular-cochain sheaves. -/
def globalSingularSheafRestriction :
    globalSingularCochainSheafComplex R X ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (singularRestrictionSheafComplex R j))

/-- The sheafification unit evaluated after restriction to the inverse image of the top open. -/
def globalRawPushforwardToSingularSheaf :
    globalRawPushforwardSingularCochainComplex R j ⟶
      globalPushforwardSingularCochainSheafComplex R j :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      ((((Functor.whiskeringLeft _ _ _).obj (Opens.map j).op).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (singularCochainSheafificationUnit R U))

/-- The double-plus presentation of the comparison is the chosen sheafification unit in each
degree. -/
lemma topOpenToGlobalSingularCochainSheafComplex_f (n : ℕ) :
    (topOpenToGlobalSingularCochainSheafComplex R X).f n =
      (toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf R X n)).app (.op ⊤) := by
  change ((singularCochainToPlusPlusPresheafComplex R X).f n ≫
      (singularCochainPlusPlusPresheafComplexIsoSheafComplex R X).hom.f n).app
        (.op ⊤) = _
  rw [singularCochainToPlusPlusPresheafComplex_f]
  change ((Opens.grothendieckTopology X).toSheafify
      (singularCochainPresheaf R X n) ≫
    (plusPlusIsoSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat (singularCochainPresheaf R X n)).hom).app (.op ⊤) = _
  rw [toSheafify_plusPlusIsoSheafify_hom]

/-- Global restriction commutes strictly with sheafification. -/
lemma globalSingularSheafRestriction_naturality :
    topOpenToGlobalSingularCochainSheafComplex R X ≫
        globalSingularSheafRestriction R j =
      globalRawSingularRestriction R j ≫
        globalRawPushforwardToSingularSheaf R j := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    topOpenToGlobalSingularCochainSheafComplex_f]
  exact congrArg (fun f ↦ f.app (.op ⊤))
    (toSheafify_comp_singularRestrictionSheaf R j n)

end AlgebraicTopology.Singular
