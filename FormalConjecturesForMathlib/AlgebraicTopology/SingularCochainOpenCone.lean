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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCochainOpenSections
public import FormalConjecturesForMathlib.AlgebraicTopology.MappingConeQuasiIso
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeCochainCone
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeCochainConeNaturality
public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiSupportSingularGlobalComparison
public import FormalConjecturesForMathlib.Algebra.Homology.MapExtendNaturality

/-! # Local singular-cochain restriction cones

The comparison is the cone map of the actual sheafification units and
actual restriction maps. Cone degree `n - 1` computes relative degree `n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

local instance singularCochainOpenConeDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

/-- The local raw cochain restriction cone, extended by zero in negative degrees. -/
def openRawSingularRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
      ComplexShape.embeddingUpNat)

/-- The local sheaf-section restriction cone. -/
def openSingularSheafRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    CochainComplex AddCommGrpCat ℤ :=
  CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
      ComplexShape.embeddingUpNat)

/-- Local supported cohomology in negative degrees vanishes already
termwise in this nonnegative sheaf-cochain model. The cone index is `n - 1`. -/
lemma openSingularSheafRestrictionCone_homology_isZero_negative
    {V W : Opens X} (i : W ⟶ V) (n : ℤ) (hn : n < 0) :
    IsZero ((openSingularSheafRestrictionCone R X i).homology (n - 1)) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change IsZero ((CochainComplex.mappingCone
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
      ComplexShape.embeddingUpNat)).X (n - 1))
  rw [CochainComplex.mappingCone.isZero_X_iff]
  constructor
  · exact (openSingularCochainSheafComplex R X V).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1 + 1; omega)
  · exact (openSingularCochainSheafComplex R X W).isZero_extend_X
      ComplexShape.embeddingUpNat _ (by intro m; change (m : ℤ) ≠ n - 1; omega)

/-- The actual local sheafification restriction square, after extension by zero. -/
lemma openSingularSheafRestrictionInt_naturality {V W : Opens X} (i : W ⟶ V) :
    HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X W)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
        ComplexShape.embeddingUpNat := by
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
    openSingularSheafRestriction_naturality]

/-- The local cone comparison induced by the actual sheafification units. -/
def openRawToSingularSheafRestrictionCone {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestrictionCone R X i ⟶ openSingularSheafRestrictionCone R X i :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X W)
      ComplexShape.embeddingUpNat)
    (openSingularSheafRestrictionInt_naturality R X i)

/-- Both local open spaces being paracompact Hausdorff suffices for the
actual cone comparison to be a quasi-isomorphism. -/
theorem openRawToSingularSheafRestrictionCone_quasiIso {V W : Opens X} (i : W ⟶ V)
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W] :
    QuasiIso (openRawToSingularSheafRestrictionCone ℚ X i) := by
  let := openRawToSingularCochainSheafComplex_quasiIso X V
  let := openRawToSingularCochainSheafComplex_quasiIso X W
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso _ _ _ _ _

/-- The local cone comparison preserves Mathlib's connecting morphism,
including its negative-first-projection convention. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionCone_connecting {V W : Opens X} (i : W ⟶ V) :
    openRawToSingularSheafRestrictionCone R X i ≫
      (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openSingularSheafRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ =
    (CochainComplex.mappingCone.triangle
        (HomologicalComplex.extendMap (openRawSingularRestriction R X i)
          ComplexShape.embeddingUpNat)).mor₃ ≫
      (HomologicalComplex.extendMap (openRawToSingularCochainSheafComplex R X V)
        ComplexShape.embeddingUpNat)⟦(1 : ℤ)⟧' :=
  (CochainComplex.mappingCone.triangleMap _ _ _ _
    (openSingularSheafRestrictionInt_naturality R X i)).comm₃.symm

/-- The actual topological pair consisting of two nested ambient opens. -/
def openInclusionPair {V W : Opens X} (i : W ⟶ V) : TopPair :=
  TopPair.of ((Opens.toTopCat X).map i)
    (Topology.IsEmbedding.of_comp ((Opens.toTopCat X).map i).hom.continuous
      V.inclusion'.hom.continuous W.isOpenEmbedding.isEmbedding)

set_option backward.isDefEq.respectTransparency false in
/-- Raw sections are the actual dual singular complex of the open space. -/
def openRawSingularCochainComplexIsoDual (V : Opens X) :
    openRawSingularCochainComplex R X V ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
        (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (AddEquiv.refl (OpenCochains R X (.op V) n)).toAddCommGrpIso) (by
      intro n m h
      obtain rfl := h
      dsimp only [openRawSingularCochainComplex]
      rw [Functor.mapHomologicalComplex_obj_d,
        Functor.mapHomologicalComplex_obj_d,
        singularCochainPresheafComplex_d,
        HomologicalComplex.linearDualCochainComplex_d]
      ext φ
      rfl)

/-- The preceding identification preserves the literal dual of the
singular-chain inclusion of nested opens. -/
lemma openRawSingularRestriction_transport {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestriction R X i ≫ (openRawSingularCochainComplexIsoDual R X W).hom =
      (openRawSingularCochainComplexIsoDual R X V).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
          (HomologicalComplex.linearDualMap
            ((chainPairFunctor R).obj (openInclusionPair X i)).hom) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rfl

/-- The actual raw cochains on an ambient open, in the integer-indexed
presentation used by relative cohomology. -/
def openRawSingularCochainComplexIntIsoDual (V : Opens X) :
    (openRawSingularCochainComplex R X V).extend ComplexShape.embeddingUpNat ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        ((SingularChainComplex R (TopCat.of V)).linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat) :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
    (openRawSingularCochainComplexIsoDual R X V) ≪≫
      (HomologicalComplex.mapExtendIso (forget₂ (ModuleCat R) AddCommGrpCat)
        (SingularChainComplex R (TopCat.of V)).linearDualCochainComplex
        ComplexShape.embeddingUpNat).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The integer comparison preserves the original pair's restriction map. -/
lemma openRawSingularRestrictionInt_transport {V W : Opens X} (i : W ⟶ V) :
    HomologicalComplex.extendMap (openRawSingularRestriction R X i)
        ComplexShape.embeddingUpNat ≫
      (openRawSingularCochainComplexIntIsoDual R X W).hom =
    (openRawSingularCochainComplexIntIsoDual R X V).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (relativeCochainRestrictionInt R (openInclusionPair X i)) := by
  dsimp only [openRawSingularCochainComplexIntIsoDual, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  change (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
    (openRawSingularRestriction R X i) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp, openRawSingularRestriction_transport,
    Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg
    (fun f => HomologicalComplex.extendMap
      (openRawSingularCochainComplexIsoDual R X V).hom ComplexShape.embeddingUpNat ≫ f)
    (HomologicalComplex.mapExtendIso_inv_naturality
      (forget₂ (ModuleCat R) AddCommGrpCat)
      (HomologicalComplex.linearDualMap
        ((chainPairFunctor R).obj (openInclusionPair X i)).hom)
      ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The raw local cone is the relative-cochain cone, via its actual
restriction square. -/
def openRawSingularRestrictionConeIsoRelative {V W : Opens X} (i : W ⟶ V) :
    openRawSingularRestrictionCone R X i ≅
      CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R (openInclusionPair X i))) :=
  HomologicalComplex.homotopyCofiber.mapArrowIso _ _
    (fun j => ⟨j - 1, ComplexShape.up_mk _ _ (by lia)⟩)
    (Arrow.isoMk (openRawSingularCochainComplexIntIsoDual R X V)
      (openRawSingularCochainComplexIntIsoDual R X W)
      (openRawSingularRestrictionInt_transport R X i).symm)

/-- The raw local cone computes relative cohomology of the literal
embedded pair `(V, W)`. -/
def openRawSingularRestrictionConeCohomologyEquivRelative {V W : Opens X}
    (i : W ⟶ V) (n : ℕ) :
    (openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1) ≃+
      RelativeCohomology R (openInclusionPair X i) n :=
  (HomologicalComplex.homologyMapIso
    (openRawSingularRestrictionConeIsoRelative R X i) ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (HomologicalComplex.homologyMapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (relativeCochainRestrictionInt R (openInclusionPair X i))
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm ((n : ℤ) - 1)).addCommGroupIsoToAddEquiv
    |>.trans <|
  (ShortComplex.mapHomologyIso
    ((CochainComplex.mappingCone
      (relativeCochainRestrictionInt R (openInclusionPair X i))).sc ((n : ℤ) - 1))
    (forget₂ (ModuleCat R) AddCommGrpCat)).addCommGroupIsoToAddEquiv
    |>.trans (relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n).toAddEquiv

/-- Sections of the actual singular sheaf restriction cone compute
relative rational cohomology. Apply to `Opens.infLELeft V U` for `(V, V ∩ U)`. -/
def openSingularSheafRestrictionConeCohomologyEquivRelative {V W : Opens X}
    (i : W ⟶ V) [ParacompactSpace V] [T2Space V]
    [ParacompactSpace W] [T2Space W] (n : ℕ) :
    (openSingularSheafRestrictionCone ℚ X i).homology ((n : ℤ) - 1) ≃+
      RelativeCohomology ℚ (openInclusionPair X i) n := by
  let := openRawToSingularSheafRestrictionCone_quasiIso X i
  exact (asIso (HomologicalComplex.homologyMap
    (openRawToSingularSheafRestrictionCone ℚ X i) ((n : ℤ) - 1))).symm.addCommGroupIsoToAddEquiv
    |>.trans (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n)

end AlgebraicTopology.Singular
