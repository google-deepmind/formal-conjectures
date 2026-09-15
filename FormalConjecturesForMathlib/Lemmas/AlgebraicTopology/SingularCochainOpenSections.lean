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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainOpenSections

/-!
# SingularCochainOpenSections

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainOpenSections`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic/global comparison retains the actual sheafification unit. -/
@[reassoc]
lemma openRawToSingularCochainSheafComplex_global (V : Opens X) :
    openRawToSingularCochainSheafComplex R X V ≫
      (openSingularCochainSheafComplexIsoGlobal R X V).hom =
    (openRawSingularCochainComplexIsoGlobal R X V).hom ≫
      topOpenToGlobalSingularCochainSheafComplex R (TopCat.of V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf R X n)).app
      (.op V) ≫
      ((singularCochainSheaf R X n).obj.map (openSubspaceImageTopIso X V).hom.op ≫
        (singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤)) =
    ((singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
      (singularCochainPresheafOpenRestrictionIso R X V n).hom.app (.op ⊤)) ≫ _
  calc
    _ = (singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
        (toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X n)).app
            (.op (V.isOpenEmbedding.functor.obj ⊤)) ≫
        (singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤) :=
      ((toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf R X n)).naturality_assoc
          (openSubspaceImageTopIso X V).hom.op _).symm
    _ = _ := by
      rw [Category.assoc, topOpenToGlobalSingularCochainSheafComplex_f]
      exact congrArg
        (fun f => (singularCochainPresheaf R X n).map
          (openSubspaceImageTopIso X V).hom.op ≫ f.app (.op ⊤))
        (toSheafify_singularCochainSheafOpenRestrictionIso R X V n)

/-- On any paracompact Hausdorff ambient open, raw rational singular
cochains map quasi-isomorphically to sections of the actual singular sheaf.
No separation or paracompactness assumption is made on the rest of `X`. -/
theorem openRawToSingularCochainSheafComplex_quasiIso (V : Opens X)
    [ParacompactSpace V] [T2Space V] :
    QuasiIso (openRawToSingularCochainSheafComplex ℚ X V) := by
  have := topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := TopCat.of V)
  have : QuasiIso
      ((openRawSingularCochainComplexIsoGlobal ℚ X V).hom ≫
        topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of V)) := inferInstance
  rw [← openRawToSingularCochainSheafComplex_global] at this
  exact (quasiIso_iff_comp_right _ _).mp this

/-- The open-section comparisons commute with the literal restriction maps.
In particular this applies to `W = V ⊓ U`. -/
@[reassoc]
lemma openSingularSheafRestriction_naturality {V W : Opens X} (i : W ⟶ V) :
    openRawToSingularCochainSheafComplex R X V ≫ openSingularSheafRestriction R X i =
      openRawSingularRestriction R X i ≫ openRawToSingularCochainSheafComplex R X W := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((toSheafify (Opens.grothendieckTopology X)
    (singularCochainPresheaf R X n)).naturality i.op).symm

end AlgebraicTopology.Singular
