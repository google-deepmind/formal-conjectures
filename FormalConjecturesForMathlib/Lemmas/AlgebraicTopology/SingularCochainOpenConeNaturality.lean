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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCochainOpenCone
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

/-! # Actual local restriction-cone naturality -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})
  {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V') (a : V' ⟶ V) (b : W' ⟶ W)

/-- The actual map of pairs induced by a square of ambient open inclusions. -/
def openInclusionPairMap : openInclusionPair X i' ⟶ openInclusionPair X i :=
  TopPair.ofHom ((Opens.toTopCat X).map a) ((Opens.toTopCat X).map b) (by ext x; rfl)

/-- Restriction of raw cochains around an actual open-inclusion square. -/
lemma openRawSingularRestriction_square :
    openRawSingularRestriction R X i ≫ openRawSingularRestriction R X b =
      openRawSingularRestriction R X a ≫ openRawSingularRestriction R X i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (singularCochainPresheaf R X n).map i.op ≫
      (singularCochainPresheaf R X n).map b.op =
    (singularCochainPresheaf R X n).map a.op ≫
      (singularCochainPresheaf R X n).map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Actual sheaf-section restriction around the same square. -/
lemma openSingularSheafRestriction_square :
    openSingularSheafRestriction R X i ≫ openSingularSheafRestriction R X b =
      openSingularSheafRestriction R X a ≫ openSingularSheafRestriction R X i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (singularCochainSheaf R X n).obj.map i.op ≫
      (singularCochainSheaf R X n).obj.map b.op =
    (singularCochainSheaf R X n).obj.map a.op ≫
      (singularCochainSheaf R X n).obj.map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Actual restriction on raw local cones. -/
def openRawSingularRestrictionConeMap :
    openRawSingularRestrictionCone R X i ⟶ openRawSingularRestrictionCone R X i' :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (openRawSingularRestriction R X a) ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openRawSingularRestriction R X b) ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      openRawSingularRestriction_square R X i i' a b])

/-- Actual restriction on sheaf-section local cones. -/
def openSingularSheafRestrictionConeMap :
    openSingularSheafRestrictionCone R X i ⟶ openSingularSheafRestrictionCone R X i' :=
  CochainComplex.mappingCone.map _ _
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X a) ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openSingularSheafRestriction R X b) ComplexShape.embeddingUpNat)
    (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
      openSingularSheafRestriction_square R X i i' a b])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual local cone sheafification map is natural in the ambient open. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionCone_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      openRawToSingularSheafRestrictionCone R X i' =
    openRawToSingularSheafRestrictionCone R X i ≫
      openSingularSheafRestrictionConeMap R X i i' a b := by
  dsimp only [openRawSingularRestrictionConeMap, openSingularSheafRestrictionConeMap,
    openRawToSingularSheafRestrictionCone]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1 <;> rw [← HomologicalComplex.extendMap_comp,
    ← HomologicalComplex.extendMap_comp, openSingularSheafRestriction_naturality]

/-- The open raw-cone identification is exactly the standard cone map
with its prescribed two components. -/
lemma openRawSingularRestrictionConeIsoRelative_hom :
    (openRawSingularRestrictionConeIsoRelative R X i).hom =
    CochainComplex.mappingCone.map _ _
      (openRawSingularCochainComplexIntIsoDual R X V).hom
      (openRawSingularCochainComplexIntIsoDual R X W).hom
      (openRawSingularRestrictionInt_transport R X i) :=
  CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual relative cone map after forgetting scalars termwise. -/
def forgottenRelativeCochainConeMap {P Q : TopPair.{0}} (f : P ⟶ Q) :
    CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R Q)) ⟶
      CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeCochainRestrictionInt R P)) :=
  CochainComplex.mappingCone.map _ _
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
      (relativeDualCochainShortComplexIntMap R f).τ₂)
    (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
      (relativeDualCochainShortComplexIntMap R f).τ₃)
    (by rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
          (relativeDualCochainShortComplexIntMap R f).comm₂₃.symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual open raw-cone comparison preserves maps of open pairs. -/
@[reassoc]
lemma openRawSingularRestrictionConeIsoRelative_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      (openRawSingularRestrictionConeIsoRelative R X i').hom =
    (openRawSingularRestrictionConeIsoRelative R X i).hom ≫
      forgottenRelativeCochainConeMap R (openInclusionPairMap X i i' a b) := by
  rw [openRawSingularRestrictionConeIsoRelative_hom,
    openRawSingularRestrictionConeIsoRelative_hom]
  dsimp only [openRawSingularRestrictionConeMap, forgottenRelativeCochainConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  · exact openRawSingularRestrictionInt_transport R X a
  · exact openRawSingularRestrictionInt_transport R X b

/-- The raw local cone identified with the forgotten relative cone,
including the canonical comparison for forgetting scalars. -/
def openRawSingularRestrictionConeIsoForgottenRelative :
    openRawSingularRestrictionCone R X i ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone (relativeCochainRestrictionInt R (openInclusionPair X i))) :=
  openRawSingularRestrictionConeIsoRelative R X i ≪≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso
      (relativeCochainRestrictionInt R (openInclusionPair X i))
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the complete chain-level open raw-cone comparison. -/
@[reassoc]
lemma openRawSingularRestrictionConeIsoForgottenRelative_naturality :
    openRawSingularRestrictionConeMap R X i i' a b ≫
      (openRawSingularRestrictionConeIsoForgottenRelative R X i').hom =
    (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
        (relativeCochainConeMap R (openInclusionPairMap X i i' a b)) := by
  dsimp only [openRawSingularRestrictionConeIsoForgottenRelative, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, openRawSingularRestrictionConeIsoRelative_naturality, Category.assoc,
    Category.assoc]
  apply congrArg (fun f => (openRawSingularRestrictionConeIsoRelative R X i).hom ≫ f)
  apply (cancel_mono (CochainComplex.mappingCone.mapHomologicalComplexIso
    (relativeCochainRestrictionInt R (openInclusionPair X i'))
    (forget₂ (ModuleCat R) AddCommGrpCat)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [relativeCochainConeMap]
  rw [CochainComplex.mappingCone.mapHomologicalComplexIso_naturality,
    Iso.inv_hom_id_assoc]
  rfl

/-- The actual homology comparison, retaining the scalar-forgetting
homology isomorphism as a separate canonical factor. -/
def openRawSingularRestrictionConeHomologyIso (n : ℤ) :
    (openRawSingularRestrictionCone R X i).homology n ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        ((CochainComplex.mappingCone
          (relativeCochainRestrictionInt R (openInclusionPair X i))).homology n) :=
  HomologicalComplex.homologyMapIso
    (openRawSingularRestrictionConeIsoForgottenRelative R X i) n ≪≫
      ShortComplex.mapHomologyIso
        ((CochainComplex.mappingCone
          (relativeCochainRestrictionInt R (openInclusionPair X i))).sc n)
        (forget₂ (ModuleCat R) AddCommGrpCat)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The complete raw-cone homology comparison preserves actual restrictions. -/
@[reassoc]
lemma openRawSingularRestrictionConeHomologyIso_naturality (n : ℤ) :
    HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b) n ≫
      (openRawSingularRestrictionConeHomologyIso R X i' n).hom =
    (openRawSingularRestrictionConeHomologyIso R X i n).hom ≫
      (forget₂ (ModuleCat R) AddCommGrpCat).map
        (HomologicalComplex.homologyMap
          (relativeCochainConeMap R (openInclusionPairMap X i i' a b)) n) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n
  change H.map (openRawSingularRestrictionConeMap R X i i' a b) ≫
      (H.map (openRawSingularRestrictionConeIsoForgottenRelative R X i').hom ≫ _) =
    (H.map (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫ _) ≫ _
  rw [← Category.assoc, ← H.map_comp,
    openRawSingularRestrictionConeIsoForgottenRelative_naturality, H.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (fun f => H.map
    (openRawSingularRestrictionConeIsoForgottenRelative R X i).hom ≫ f)
    (ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) n).map
        (relativeCochainConeMap R (openInclusionPairMap X i i' a b)))
      (forget₂ (ModuleCat R) AddCommGrpCat))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The previously exposed open-cone equivalence factors through this
canonical homology comparison and the natural relative evaluation pairing. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_eq (n : ℕ)
    (z : (openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1)) :
    openRawSingularRestrictionConeCohomologyEquivRelative R X i n z =
      relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n
        ((openRawSingularRestrictionConeHomologyIso R X i ((n : ℤ) - 1)).hom z) := by
  let eA := openRawSingularRestrictionConeIsoRelative R X i
  let eB := CochainComplex.mappingCone.mapHomologicalComplexIso
    (relativeCochainRestrictionInt R (openInclusionPair X i))
    (forget₂ (ModuleCat R) AddCommGrpCat)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) ((n : ℤ) - 1)
  change relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n
    ((ShortComplex.mapHomologyIso _ (forget₂ (ModuleCat R) AddCommGrpCat)).hom
      (H.map eB.inv (H.map eA.hom z))) =
    relativeCochainConeCohomologyEquivCanonical R (openInclusionPair X i) n
      ((ShortComplex.mapHomologyIso _ (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        (H.map (eA.hom ≫ eB.inv) z))
  rw [H.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exact relative-cohomology naturality of the actual local raw-cone
comparison, including all grading and scalar-forgetting identifications. -/
lemma openRawSingularRestrictionConeCohomologyEquivRelative_naturality (n : ℕ)
    (z : (openRawSingularRestrictionCone R X i).homology ((n : ℤ) - 1)) :
    openRawSingularRestrictionConeCohomologyEquivRelative R X i' n
        (HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b)
          ((n : ℤ) - 1) z) =
      relativeCohomologyMap R n (openInclusionPairMap X i i' a b)
        (openRawSingularRestrictionConeCohomologyEquivRelative R X i n z) := by
  rw [openRawSingularRestrictionConeCohomologyEquivRelative_eq,
    openRawSingularRestrictionConeCohomologyEquivRelative_eq]
  have h := ConcreteCategory.congr_hom
    (openRawSingularRestrictionConeHomologyIso_naturality R X i i' a b ((n : ℤ) - 1)) z
  change (openRawSingularRestrictionConeHomologyIso R X i' ((n : ℤ) - 1)).hom
      (HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap R X i i' a b)
        ((n : ℤ) - 1) z) =
    HomologicalComplex.homologyMap (relativeCochainConeMap R (openInclusionPairMap X i i' a b))
      ((n : ℤ) - 1) ((openRawSingularRestrictionConeHomologyIso R X i ((n : ℤ) - 1)).hom z) at h
  rw [h]
  exact relativeCochainConeCohomologyEquivCanonical_naturality _ _ _ _

/-- Homology of the actual raw-to-sheaf cone map. -/
def openRawToSingularSheafRestrictionConeHomologyIso
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W] (n : ℤ) :
    (openRawSingularRestrictionCone ℚ X i).homology n ≅
      (openSingularSheafRestrictionCone ℚ X i).homology n := by
  let := openRawToSingularSheafRestrictionCone_quasiIso X i
  exact asIso (HomologicalComplex.homologyMap (openRawToSingularSheafRestrictionCone ℚ X i) n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inverting the actual sheafification quasi-isomorphism preserves the
literal local restriction square. -/
@[reassoc]
lemma openRawToSingularSheafRestrictionConeHomologyIso_inv_naturality
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W]
    [ParacompactSpace V'] [T2Space V'] [ParacompactSpace W'] [T2Space W'] (n : ℤ) :
    HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b) n ≫
      (openRawToSingularSheafRestrictionConeHomologyIso X i' n).inv =
    (openRawToSingularSheafRestrictionConeHomologyIso X i n).inv ≫
      HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b) n := by
  have h := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).map
    (openRawToSingularSheafRestrictionCone_naturality ℚ X i i' a b)
  rw [Functor.map_comp, Functor.map_comp] at h
  change HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b) n ≫
      (openRawToSingularSheafRestrictionConeHomologyIso X i' n).hom =
    (openRawToSingularSheafRestrictionConeHomologyIso X i n).hom ≫
      HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b) n at h
  apply (cancel_mono (openRawToSingularSheafRestrictionConeHomologyIso X i' n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The complete actual local sheaf-section cone comparison intertwines
ambient-open restriction with the literal relative-cohomology pullback. -/
lemma openSingularSheafRestrictionConeCohomologyEquivRelative_naturality
    [ParacompactSpace V] [T2Space V] [ParacompactSpace W] [T2Space W]
    [ParacompactSpace V'] [T2Space V'] [ParacompactSpace W'] [T2Space W'] (n : ℕ)
    (z : (openSingularSheafRestrictionCone ℚ X i).homology ((n : ℤ) - 1)) :
    openSingularSheafRestrictionConeCohomologyEquivRelative X i' n
        (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
          ((n : ℤ) - 1) z) =
      relativeCohomologyMap ℚ n (openInclusionPairMap X i i' a b)
        (openSingularSheafRestrictionConeCohomologyEquivRelative X i n z) := by
  change openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i' n
      ((openRawToSingularSheafRestrictionConeHomologyIso X i' ((n : ℤ) - 1)).inv
        (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
          ((n : ℤ) - 1) z)) =
    relativeCohomologyMap ℚ n (openInclusionPairMap X i i' a b)
      (openRawSingularRestrictionConeCohomologyEquivRelative ℚ X i n
        ((openRawToSingularSheafRestrictionConeHomologyIso X i ((n : ℤ) - 1)).inv z))
  have h := ConcreteCategory.congr_hom
    (openRawToSingularSheafRestrictionConeHomologyIso_inv_naturality X i i' a b
      ((n : ℤ) - 1)) z
  change (openRawToSingularSheafRestrictionConeHomologyIso X i' ((n : ℤ) - 1)).inv
      (HomologicalComplex.homologyMap (openSingularSheafRestrictionConeMap ℚ X i i' a b)
        ((n : ℤ) - 1) z) =
    HomologicalComplex.homologyMap (openRawSingularRestrictionConeMap ℚ X i i' a b)
      ((n : ℤ) - 1) ((openRawToSingularSheafRestrictionConeHomologyIso X i ((n : ℤ) - 1)).inv z) at h
  rw [h]
  exact openRawSingularRestrictionConeCohomologyEquivRelative_naturality _ _ _ _ _ _ _ _

end AlgebraicTopology.Singular
