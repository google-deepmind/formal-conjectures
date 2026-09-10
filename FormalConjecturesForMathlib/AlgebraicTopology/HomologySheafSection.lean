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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularChainHomologySheaf

/-!
# Sections of the homology sheaf from actual relative homology

Exact sheafification sends presheaf homology to the actual homology sheaf. The unit
therefore sends a relative singular homology class on an open support to a section of
the homology sheaf. The germ comparison records the actual restriction to local relative
homology, which is essential for preserving normalized fundamental classes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomologicalComplex Opposite

universe u

namespace CategoryTheory.ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homology comparison is compatible with composition of exact functors. -/
@[reassoc]
theorem mapHomologyIso_comp_hom (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  rw [(S.homologyData.left.map F).mapHomologyIso_eq G]
  simp only [mapHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  erw [Category.comp_id]
  let γ : LeftHomologyMapData (𝟙 (S.map (F ⋙ G)))
      (S.homologyData.left.map (F ⋙ G)) ((S.homologyData.left.map F).map G) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp
      commπ := by simp }
  simpa only [γ, homologyMap_id, Category.id_comp, Category.comp_id] using
    γ.homologyMap_comm.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural transformation into a composite exact functor respects the two successive
canonical homology comparisons. -/
@[reassoc]
theorem homology_comparison_of_natTrans (S : ShortComplex C)
    (P : C ⥤ E) (F : C ⥤ D) (G : D ⥤ E)
    [P.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (τ : P ⟶ F ⋙ G) :
    τ.app S.homology ≫ G.map (S.mapHomologyIso F).inv ≫
      ((S.map F).mapHomologyIso G).inv =
      (S.mapHomologyIso P).inv ≫ ShortComplex.homologyMap (S.mapNatTrans τ) := by
  rw [NatTrans.app_homology τ S, mapHomologyIso_comp_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map (S.mapHomologyIso F).hom) (G.map (S.mapHomologyIso F).inv),
    ← G.map_comp, Iso.hom_inv_id, G.map_id, Category.id_comp, Iso.hom_inv_id,
    Category.comp_id]

end CategoryTheory.ShortComplex

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The stalk functor with its domain displayed as a functor category, to align the
canonical additive structures used in functor-category homology comparisons. -/
abbrev additivePresheafStalkFunctor (x : X) :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance additivePresheafStalkFunctor_additive (x : X) :
    (additivePresheafStalkFunctor X x).Additive where
  map_add := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add

/-- The exact sheaf stalk functor, with the categorical sheaf domain displayed. -/
abbrev additiveSheafStalkFunctor (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance additiveSheafStalkFunctor_additive (x : X) :
    (additiveSheafStalkFunctor X x).Additive where
  map_add := (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_add

instance additiveSheafStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (additiveSheafStalkFunctor X x) := by
  change PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  infer_instance

instance additiveSheafStalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (additiveSheafStalkFunctor X x) := by
  change PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Sheafification leaves stalks unchanged, naturally in the additive presheaf. -/
def additivePresheafStalkSheafificationIso (x : X) :
    additivePresheafStalkFunctor X x ≅
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        additiveSheafStalkFunctor X x :=
  NatIso.ofComponents (fun P ↦ by
    letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
    exact asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))) (by
    intro P Q f
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toSheafify _ Q) =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (toSheafify _ P) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (sheafifyMap _ f)
    simpa only [Functor.map_comp] using
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).congr_map
        (toSheafify_naturality (Opens.grothendieckTopology X) f))

instance additivePresheafStalkFunctor_preservesFiniteLimits (x : X) :
    PreservesFiniteLimits (additivePresheafStalkFunctor X x) :=
  preservesFiniteLimits_of_natIso (additivePresheafStalkSheafificationIso X x).symm

instance additivePresheafStalkFunctor_preservesFiniteColimits (x : X) :
    PreservesFiniteColimits (additivePresheafStalkFunctor X x) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))

/-- Evaluation of the presheaf chain complex is the actual relative chain complex. -/
def singularChainPresheafComplexEvaluationIso (U : Opens X) :
    (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (.down ℕ)).obj (singularChainPresheafComplex R X) ≅
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.down ℕ)).obj
        ((relativeChainFunctor R).obj (TopPair.ofSubset (U : Set X)ᶜ)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    obtain rfl := hij
    change _ ≫ _ = ((singularChainPresheafComplex R X).d (j + 1) j).app (op U) ≫ _
    rw [singularChainPresheafComplex_d]
    simp only [Iso.refl_hom]
    rfl)

/-- Actual relative homology identifies with the evaluation of the homology presheaf. -/
def relativeHomologyPresheafSectionIso (U : Opens X) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
      (RelativeHomology R (TopPair.ofSubset (U : Set X)ᶜ) n) ≅
      ((singularChainPresheafComplex R X).homology n).obj (op U) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (singularChainPresheafComplex R X).sc n
  let e := S.mapHomologyIso
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))
  exact ((((relativeChainFunctor R).obj (TopPair.ofSubset (U : Set X)ᶜ)).sc n).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    (homologyMapIso (singularChainPresheafComplexEvaluationIso R X U) n).symm ≪≫
      e

/-- Exact sheafification identifies the sheafification of presheaf homology with the
homology sheaf of the actual relative-chain model. -/
def singularChainHomologySheafificationIso (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      ((singularChainPresheafComplex R X).homology n) ≅
      singularChainHomologySheaf R X n := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (singularChainPresheafComplex R X).sc n
  let e := S.mapHomologyIso
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  exact e.symm

/-- The canonical map from presheaf homology to the actual homology sheaf. -/
def singularChainHomologyPresheafToSheaf (n : ℕ) :
    (singularChainPresheafComplex R X).homology n ⟶
      (singularChainHomologySheaf R X n).presheaf :=
  toSheafify (Opens.grothendieckTopology X) _ ≫
    (singularChainHomologySheafificationIso R X n).hom.hom

/-- An actual relative homology class on an open support gives a section of the
homology sheaf; this map is constructed by exact sheafification. -/
def relativeHomologyToHomologySheafSection (U : Opens X) (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
      (RelativeHomology R (TopPair.ofSubset (U : Set X)ᶜ) n) ⟶
      (singularChainHomologySheaf R X n).presheaf.obj (op U) :=
  (relativeHomologyPresheafSectionIso R X U n).hom ≫
    (singularChainHomologyPresheafToSheaf R X n).app (op U)

/-- The germ maps, as a natural transformation from evaluation to the stalk functor. -/
def additivePresheafGermNatTrans (U : Opens X) (x : X) (hx : x ∈ U) :
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ⟶
      additivePresheafStalkFunctor X x where
  app P := TopCat.Presheaf.germ P U x hx
  naturality {_P _Q} f := (TopCat.Presheaf.stalkFunctor_map_germ U x hx f).symm

/-- Presheaf homology stalks identify with actual local relative homology. -/
def singularChainHomologyPresheafStalkIso [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      ((singularChainPresheafComplex R X).homology n) ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        (RelativeHomology R (TopPair.ofSubset ({x} : Set X)ᶜ) n) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (singularChainPresheafComplex R X).sc n
  exact (S.mapHomologyIso (additivePresheafStalkFunctor X x)).symm ≪≫
    homologyMapIso (singularChainPresheafComplexStalkIso R X x) n ≪≫
      (((relativeChainFunctor R).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).sc n).mapHomologyIso
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- The evaluated germ chain map is the actual restriction to the point complement. -/
@[reassoc]
theorem singularChainPresheafComplexEvaluationIso_germ [T2Space X]
    (U : Opens X) (x : X) (hx : x ∈ U) :
    (singularChainPresheafComplexEvaluationIso R X U).inv ≫
      ((additivePresheafGermNatTrans X U x hx).mapHomologicalComplex (.down ℕ)).app
        (singularChainPresheafComplex R X) ≫
      (singularChainPresheafComplexStalkIso R X x).hom =
      ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.down ℕ)).map
        ((relativeChainFunctor R).map
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))) := by
  apply HomologicalComplex.hom_ext
  intro n
  change 𝟙 _ ≫ (singularChainPresheaf R X n).germ U x hx ≫
    (singularChainPresheafStalkIso R X x n).hom = _
  rw [Category.id_comp, singularChainPresheafStalkIso_germ]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The germ of a relative class in the homology presheaf is exactly its actual
restriction to the local pair. -/
@[reassoc]
theorem relativeHomologyPresheafSectionIso_germ [T2Space X]
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    (relativeHomologyPresheafSectionIso R X U n).hom ≫
      TopCat.Presheaf.germ ((singularChainPresheafComplex R X).homology n) U x hx ≫
      (singularChainHomologyPresheafStalkIso R X x n).hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (ModuleCat.ofHom (relativeHomologyMap R n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)))) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (singularChainPresheafComplex R X).sc n
  let τ := additivePresheafGermNatTrans X U x hx
  have hτ := ShortComplex.homologyMap_mapNatTrans S τ
  simp only [relativeHomologyPresheafSectionIso, singularChainHomologyPresheafStalkIso,
    Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom, homologyMapIso_inv, Category.assoc]
  erw [← reassoc_of% hτ]
  change _ ≫ HomologicalComplex.homologyMap (singularChainPresheafComplexEvaluationIso R X U).inv n ≫
    HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.down ℕ)).app
      (singularChainPresheafComplex R X)) n ≫
    HomologicalComplex.homologyMap (singularChainPresheafComplexStalkIso R X x).hom n ≫ _ = _
  rw [← homologyMap_comp_assoc (singularChainPresheafComplexEvaluationIso R X U).inv,
    ← homologyMap_comp_assoc _ (singularChainPresheafComplexStalkIso R X x).hom]
  erw [Category.assoc (singularChainPresheafComplexEvaluationIso R X U).inv,
    singularChainPresheafComplexEvaluationIso_germ]
  have hmap := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{u} R) (.down ℕ) n).map
      ((relativeChainFunctor R).map
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))))
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  erw [hmap, Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 800000 in
/-- The homology sheafification unit is compatible with the actual local-homology
identifications on stalks. -/
@[reassoc]
theorem singularChainHomologyPresheafToSheaf_stalk [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (singularChainHomologyPresheafToSheaf R X n) ≫
      (singularChainHomologySheafStalkIso R X x n).hom =
      (singularChainHomologyPresheafStalkIso R X x n).hom := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (singularChainPresheafComplex R X).sc n
  let P := additivePresheafStalkFunctor X x
  let L := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let G := additiveSheafStalkFunctor X x
  let τ := (additivePresheafStalkSheafificationIso X x).hom
  have hτ := ShortComplex.homology_comparison_of_natTrans S P L G τ
  simp only [singularChainHomologyPresheafToSheaf, singularChainHomologySheafStalkIso,
    singularChainSheafStalkHomologyIso, singularChainSheafStalkIso,
    singularChainHomologyPresheafStalkIso, Iso.trans_hom, Iso.symm_hom,
    Functor.map_comp, Functor.mapIso_hom, homologyMapIso_hom,
    Category.assoc]
  change τ.app S.homology ≫ G.map (S.mapHomologyIso L).inv ≫
    ((S.map L).mapHomologyIso G).inv ≫
    HomologicalComplex.homologyMap (singularChainSheafificationStalkIso R X x).inv n ≫
    HomologicalComplex.homologyMap (singularChainPresheafComplexStalkIso R X x).hom n ≫ _ = _
  erw [reassoc_of% hτ]
  change (S.mapHomologyIso P).inv ≫
    HomologicalComplex.homologyMap (singularChainSheafificationStalkIso R X x).hom n ≫
    HomologicalComplex.homologyMap (singularChainSheafificationStalkIso R X x).inv n ≫ _ = _
  rw [← homologyMap_comp_assoc (singularChainSheafificationStalkIso R X x).hom
    (singularChainSheafificationStalkIso R X x).inv, Iso.hom_inv_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The constructed sheaf section has, under the canonical stalk identification,
exactly the local restriction of the original relative homology class. -/
@[reassoc]
theorem relativeHomologyToHomologySheafSection_germ [T2Space X]
    (U : Opens X) (x : X) (hx : x ∈ U) (n : ℕ) :
    relativeHomologyToHomologySheafSection R X U n ≫
      (singularChainHomologySheaf R X n).presheaf.germ U x hx ≫
      (singularChainHomologySheafStalkIso R X x n).hom =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (ModuleCat.ofHom (relativeHomologyMap R n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)))) := by
  rw [relativeHomologyToHomologySheafSection, Category.assoc,
    ← TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    singularChainHomologyPresheafToSheaf_stalk,
    relativeHomologyPresheafSectionIso_germ]

end AlgebraicTopology.Singular
