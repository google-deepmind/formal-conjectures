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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainOpenRestriction
public import FormalConjecturesForMathlib.AlgebraicTopology.GlobalSingularRestriction

/-! # Singular cochains compute sheafified cochains on an arbitrary open -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

/-- Raw singular cochains evaluated on an ambient open. -/
def openRawSingularCochainComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainPresheafComplex R X)

/-- Sections on an ambient open of the actual singular cochain sheaf complex. -/
def openSingularCochainSheafComplex (V : Opens X) : CochainComplex AddCommGrpCat ℕ :=
  ((TopCat.Sheaf.supportEvaluation X V).mapHomologicalComplex (.up ℕ)).obj
    (singularCochainSheafComplex R X)

/-- The actual singular-cochain sheafification unit evaluated on an ambient open. -/
def openRawToSingularCochainSheafComplex (V : Opens X) :
    openRawSingularCochainComplex R X V ⟶ openSingularCochainSheafComplex R X V :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).mapHomologicalComplex (.up ℕ)).map
    (singularCochainSheafificationUnit R X)

/-- The image of the top open of a subspace is that ambient open itself. -/
def openSubspaceImageTopIso (V : Opens X) : V.isOpenEmbedding.functor.obj ⊤ ≅ V :=
  eqToIso (by ext x; simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Ambient raw cochains on `V` identified with top-open raw cochains of
the space `V`, through the actual image homeomorphism. -/
def openRawSingularCochainComplexIsoGlobal (V : Opens X) :
    openRawSingularCochainComplex R X V ≅ globalRawSingularCochainComplex R (TopCat.of V) :=
  (NatIso.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op)
      (.up ℕ)).app (singularCochainPresheafComplex R X) ≪≫
    (((evaluation (Opens (TopCat.of V))ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
      (.up ℕ)).mapIso (singularCochainPresheafComplexOpenRestrictionIso R X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the ambient singular sheaf on `V` identified with global
sections of its intrinsic singular sheaf, using the normalized open restriction. -/
def openSingularCochainSheafComplexIsoGlobal (V : Opens X) :
    openSingularCochainSheafComplex R X V ≅
      globalSingularCochainSheafComplex R (TopCat.of V) := by
  let : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).PreservesZeroMorphisms :=
    inferInstanceAs ((TopCat.Sheaf.supportEvaluation X V).PreservesZeroMorphisms)
  let : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj
        (.op (V.isOpenEmbedding.functor.obj ⊤))).PreservesZeroMorphisms :=
    inferInstanceAs ((TopCat.Sheaf.supportEvaluation X
      (V.isOpenEmbedding.functor.obj ⊤)).PreservesZeroMorphisms)
  exact
  (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft (TopCat.Sheaf.forget AddCommGrpCat X)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op))
      (.up ℕ)).app (singularCochainSheafComplex R X) ≪≫
    ((TopCat.Sheaf.supportEvaluation (TopCat.of V) ⊤).mapHomologicalComplex (.up ℕ)).mapIso
      (singularCochainSheafComplexOpenRestrictionIso R X V)

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

/-- Actual restriction of raw cochains between two ambient opens. -/
def openRawSingularRestriction {V W : Opens X} (i : W ⟶ V) :
    openRawSingularCochainComplex R X V ⟶ openRawSingularCochainComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (singularCochainPresheafComplex R X)

/-- Actual restriction of sections of the singular cochain sheaf. -/
def openSingularSheafRestriction {V W : Opens X} (i : W ⟶ V) :
    openSingularCochainSheafComplex R X V ⟶ openSingularCochainSheafComplex R X W :=
  (NatTrans.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).map i.op) (.up ℕ)).app
      (((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex (.up ℕ)).obj
        (singularCochainSheafComplex R X))

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
