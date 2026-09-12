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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueSheafSupportComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenInjectiveResolutionComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiSupportSingularNaturality

/-!
# Singular-cochain models for supported injective resolutions

On a space with a contractible open basis, the singular-cochain augmentation resolves the
constant rational sheaf, and we extend that augmentation to the fixed injective resolution
with a strict normalization. On a hereditarily paracompact Hausdorff space the singular model
is termwise flasque, so the supported comparison is a quasi-isomorphism on sheaves and on
every open set. The contractible basis is a hypothesis of these generic topological lemmas,
constructed for the smooth complex-point application below.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex

namespace AlgebraicTopology.Singular

variable (X : TopCat.{0})

/-- The actual singular-cochain sheaf complex in integer degrees. -/
def rationalSingularCochainComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  (singularCochainSheafComplex ℚ X).extend ComplexShape.embeddingUpNat

/-- The fixed injective resolution of actual rational constants, in integer degrees. -/
def rationalConstantInjectiveComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex.extend
    ComplexShape.embeddingUpNat

instance rationalSingularCochainComplex_isStrictlyGE :
    (rationalSingularCochainComplex X).IsStrictlyGE 0 := by
  dsimp [rationalSingularCochainComplex]
  infer_instance

instance rationalConstantInjectiveComplex_isStrictlyGE :
    (rationalConstantInjectiveComplex X).IsStrictlyGE 0 := by
  dsimp [rationalConstantInjectiveComplex]
  infer_instance

instance rationalConstantInjectiveComplex_injective (n : ℤ) :
    Injective ((rationalConstantInjectiveComplex X).X n) :=
  CochainComplex.injective_extend_nat _
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective n

variable (hX : ∀ (x : X) (V : Opens X), x ∈ V →
  ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V)

/-- Strictly extend the constant augmentation to the actual injective resolution. -/
def singularToConstantInjectiveResolution :
    singularCochainSheafComplex ℚ X ⟶
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex := by
  let : Mono (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_mono ℚ X
  let : QuasiIso (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  exact CochainComplex.liftToInjectiveNat (constantsToSingularCochainSheafComplex ℚ X)
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective

/-- The comparison fixes the prescribed rational constant augmentation exactly. -/
@[reassoc (attr := simp)]
lemma constants_comp_singularToConstantInjectiveResolution :
    constantsToSingularCochainSheafComplex ℚ X ≫ singularToConstantInjectiveResolution X hX =
      (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).ι := by
  let : Mono (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_mono ℚ X
  let : QuasiIso (constantsToSingularCochainSheafComplex ℚ X) :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  exact CochainComplex.comp_liftToInjectiveNat _ _
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective

instance singularToConstantInjectiveResolution_quasiIso :
    QuasiIso (singularToConstantInjectiveResolution X hX) := by
  let a := constantsToSingularCochainSheafComplex ℚ X
  let : QuasiIso a :=
    constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ hX
  have : QuasiIso (a ≫ singularToConstantInjectiveResolution X hX) := by
    rw [constants_comp_singularToConstantInjectiveResolution]
    exact (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).quasiIso
  exact quasiIso_of_comp_left a _

/-- The same strictly normalized comparison in integer degrees. -/
def singularToConstantInjectiveComplex :
    rationalSingularCochainComplex X ⟶ rationalConstantInjectiveComplex X :=
  HomologicalComplex.extendMap (singularToConstantInjectiveResolution X hX)
    ComplexShape.embeddingUpNat

instance singularToConstantInjectiveComplex_quasiIso :
    QuasiIso (singularToConstantInjectiveComplex X hX) :=
  (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance

/-- The actual supported singular-cochain sheaf model. Its terms are kernels
of restriction; its cohomology is not defined to be a desired purity group. -/
def supportedRationalSingularCochainComplex (U : Opens X) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj
    (rationalSingularCochainComplex X)

/-- Apply actual supported sections to the constructed resolution comparison. -/
def supportedSingularToInjectiveComplex (U : Opens X) :
    supportedRationalSingularCochainComplex X U ⟶
      ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj
        (rationalConstantInjectiveComplex X) :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).map
    (singularToConstantInjectiveComplex X hX)

variable [T2Space X] [∀ V : Opens X, ParacompactSpace V]

instance rationalSingularCochainComplex_isFlasque (n : ℤ) :
    ((rationalSingularCochainComplex X).X n).IsFlasque := by
  apply AlgebraicGeometry.ComplexPoint.extendNat_term_isFlasque
  intro m
  change (singularCochainSheaf ℚ X m).IsFlasque
  infer_instance

/-- Supported singular cochains really compute the supported injective model,
on the level of actual sheaf complexes. -/
instance supportedSingularToInjectiveComplex_quasiIso (U : Opens X) :
    QuasiIso (supportedSingularToInjectiveComplex X hX U) :=
  TopCat.Sheaf.sheafSectionsSupportedOutside_map_quasiIso_of_flasque X U
    (singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

/-- The comparison is a quasi-isomorphism on sections on every open set.
This stronger conclusion is essential for applying local normal-slice calculations. -/
theorem supportedSingularToInjectiveComplex_onOpen_quasiIso (U V : Opens X) :
    QuasiIso (((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).map
      (supportedSingularToInjectiveComplex X hX U)) :=
  TopCat.Sheaf.supportedSections_map_quasiIso_of_flasque X U V
    (singularToConstantInjectiveComplex X hX) 0 0 (fun _ => inferInstance) (fun _ => inferInstance)

/-- Actual section-complex cohomology agrees through the normalized comparison. -/
def supportedSingularInjectiveHomologyIso (U V : Opens X) (n : ℤ) :
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (supportedRationalSingularCochainComplex X U))).homology n ≅
    ((((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj
      (((TopCat.Sheaf.sheafSectionsSupportedOutside X U).mapHomologicalComplex (.up ℤ)).obj
        (rationalConstantInjectiveComplex X)))).homology n := by
  let f := ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℤ)).map
    (supportedSingularToInjectiveComplex X hX U)
  let : QuasiIso f := supportedSingularToInjectiveComplex_onOpen_quasiIso X hX U V
  exact asIso (HomologicalComplex.homologyMap f n)

end AlgebraicTopology.Singular
