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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SupportedSectionRestrictionCone
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality
public import FormalConjecturesForMathlib.Lemmas.Algebra.Homology.DerivedCategory.MappingConeMapNaturality

/-!
# Restriction naturality of the actual supported-section kernel comparison

Every map below is induced by the literal restriction of sheaf sections. In
particular the short-exact-sequence lift is the positive canonical lift; its
naturality is established before passing to homology or sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Actual section restriction around a rectangle of open inclusions. -/
lemma sectionComplexRestriction_square {I : Type*} (c : ComplexShape I)
    (K : HomologicalComplex (Sheaf AddCommGrpCat.{u} X) c)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    sectionComplexRestriction X c K i ≫ sectionComplexRestriction X c K b =
      sectionComplexRestriction X c K a ≫ sectionComplexRestriction X c K i' := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (K.X n).obj.map i.op ≫ (K.X n).obj.map b.op =
    (K.X n).obj.map a.op ≫ (K.X n).obj.map i'.op
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The literal restriction on the cones of section restriction. -/
def sectionComplexRestrictionConeMap
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    CochainComplex.mappingCone (sectionComplexRestriction X (.up ℤ) K i) ⟶
      CochainComplex.mappingCone (sectionComplexRestriction X (.up ℤ) K i') :=
  CochainComplex.mappingCone.map _ _
    (sectionComplexRestriction X (.up ℤ) K a)
    (sectionComplexRestriction X (.up ℤ) K b)
    (sectionComplexRestriction_square X (.up ℤ) K i i' a b)

variable (U : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)
  {V W : Opens X} (a : W ⟶ V)

/-- The actual map between the three terms of the supported-section sequence. -/
def supportRestrictionSectionsComplexMap :
    supportRestrictionSectionsComplexShortComplex X U V K ⟶
      supportRestrictionSectionsComplexShortComplex X U W K where
  τ₁ := sectionComplexRestriction X (.up ℤ)
    (supportRestrictionComplexShortComplex X U K).X₁ a
  τ₂ := sectionComplexRestriction X (.up ℤ) K a
  τ₃ := sectionComplexRestriction X (.up ℤ)
    (supportRestrictionComplexShortComplex X U K).X₃ a
  comm₁₂ := (((supportEvaluationRestriction X a).mapHomologicalComplex (.up ℤ)).naturality
    (supportRestrictionComplexShortComplex X U K).f).symm
  comm₂₃ := (((supportEvaluationRestriction X a).mapHomologicalComplex (.up ℤ)).naturality
    (supportRestrictionComplexShortComplex X U K).g).symm

/-- The pushforward/intersection identification commutes with literal restriction. -/
@[reassoc]
lemma supportedOutsideIntersectionIso_naturality (F : Sheaf AddCommGrpCat.{u} X) :
    ((openRestrictionPushforward X U).obj F).obj.map a.op ≫
      (supportedOutsideIntersectionIso X U W F).hom =
    (supportedOutsideIntersectionIso X U V F).hom ≫
      F.obj.map (homOfLE (inf_le_inf_right U (leOfHom a))).op := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Naturality of the actual intersection identification on coefficient complexes. -/
@[reassoc]
lemma supportRestrictionSectionsIntersectionIso_naturality :
    (supportRestrictionSectionsComplexMap X U K a).τ₃ ≫
      (supportRestrictionSectionsIntersectionIso X U W K).hom =
    (supportRestrictionSectionsIntersectionIso X U V K).hom ≫
      sectionComplexRestriction X (.up ℤ) K
        (homOfLE (inf_le_inf_right U (leOfHom a))) :=
  HomologicalComplex.Hom.ext
    (funext fun n ↦ supportedOutsideIntersectionIso_naturality X U a (K.X n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual cone identification is a standard cone map with the specified components. -/
lemma supportRestrictionSectionsConeIso_hom (V : Opens X) :
    (supportRestrictionSectionsConeIso X U V K).hom =
      CochainComplex.mappingCone.map _ _ (𝟙 _)
        (supportRestrictionSectionsIntersectionIso X U V K).hom
        (by simpa using supportRestrictionSectionsIntersectionIso_restriction X U V K) :=
  CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cone identification respects restriction of the entire supported-section sequence. -/
@[reassoc]
lemma supportRestrictionSectionsConeIso_naturality :
    CochainComplex.mappingCone.map _ _
      (supportRestrictionSectionsComplexMap X U K a).τ₂
      (supportRestrictionSectionsComplexMap X U K a).τ₃
      (supportRestrictionSectionsComplexMap X U K a).comm₂₃.symm ≫
        (supportRestrictionSectionsConeIso X U W K).hom =
    (supportRestrictionSectionsConeIso X U V K).hom ≫
      sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft W U)
        a (homOfLE (inf_le_inf_right U (leOfHom a))) := by
  rw [supportRestrictionSectionsConeIso_hom, supportRestrictionSectionsConeIso_hom]
  dsimp only [sectionComplexRestrictionConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1
  exact supportRestrictionSectionsIntersectionIso_naturality X U K a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The flasque kernel-to-cone comparison is natural on homology in the ambient open. -/
@[reassoc]
lemma supportedSectionHomologyIsoRestrictionCone_naturality
    (hK : ∀ n, (K.X n).IsFlasque) (n : ℤ) :
    HomologicalComplex.homologyMap (supportRestrictionSectionsComplexMap X U K a).τ₁ n ≫
      (supportedSectionHomologyIsoRestrictionCone X U W K hK n).hom =
    (supportedSectionHomologyIsoRestrictionCone X U V K hK n).hom ≫
      HomologicalComplex.homologyMap
        (sectionComplexRestrictionConeMap X K (Opens.infLELeft V U) (Opens.infLELeft W U)
          a (homOfLE (inf_le_inf_right U (leOfHom a)))) (n - 1) := by
  let S := supportRestrictionSectionsComplexShortComplex X U V K
  let T := supportRestrictionSectionsComplexShortComplex X U W K
  let hS := supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U V K hK
  let hT := supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque X U W K hK
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) (n - 1)
  change HomologicalComplex.homologyMap (supportRestrictionSectionsComplexMap X U K a).τ₁ n ≫
      ((CochainComplex.mappingCocone.shortExactHomologyIsoCone T hT (n - 1) n (by omega)).hom ≫
        H.map (supportRestrictionSectionsConeIso X U W K).hom) =
    ((CochainComplex.mappingCocone.shortExactHomologyIsoCone S hS (n - 1) n (by omega)).hom ≫
        H.map (supportRestrictionSectionsConeIso X U V K).hom) ≫ _
  rw [CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality_assoc
    (supportRestrictionSectionsComplexMap X U K a) hS hT (n - 1) n (by omega)]
  simp only [Category.assoc]
  congr 1
  change H.map _ ≫ H.map _ = H.map _ ≫ H.map _
  rw [← H.map_comp, ← H.map_comp, supportRestrictionSectionsConeIso_naturality]

/-- The canonical grading cone comparison is the actual map of its two grading isomorphisms. -/
lemma sectionComplexRestrictionExtendConeIso_hom
    (L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W : Opens X} (i : W ⟶ V) :
    (sectionComplexRestrictionExtendConeIso X L i).hom =
      CochainComplex.mappingCone.map _ _
        (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X V) L
          ComplexShape.embeddingUpNat).hom
        (HomologicalComplex.mapExtendCanonicalIso (supportEvaluation X W) L
          ComplexShape.embeddingUpNat).hom
        (sectionComplexRestriction_extend X L i) :=
  CochainComplex.mappingCone.mapArrowHom_eq_map _ _ _ _ _

/-- The canonical grading cone comparison respects the actual restriction rectangle. -/
@[reassoc]
lemma sectionComplexRestrictionExtendConeIso_naturality
    (L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ)
    {V W V' W' : Opens X} (i : W ⟶ V) (i' : W' ⟶ V')
    (a : V' ⟶ V) (b : W' ⟶ W) :
    sectionComplexRestrictionConeMap X (L.extend ComplexShape.embeddingUpNat) i i' a b ≫
      (sectionComplexRestrictionExtendConeIso X L i').hom =
    (sectionComplexRestrictionExtendConeIso X L i).hom ≫
      CochainComplex.mappingCone.map _ _
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) L a)
          ComplexShape.embeddingUpNat)
        (HomologicalComplex.extendMap (sectionComplexRestriction X (.up ℕ) L b)
          ComplexShape.embeddingUpNat)
        (by rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
          sectionComplexRestriction_square X (.up ℕ) L i i' a b]) := by
  rw [sectionComplexRestrictionExtendConeIso_hom, sectionComplexRestrictionExtendConeIso_hom]
  dsimp only [sectionComplexRestrictionConeMap]
  rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
  congr 1 <;> exact sectionComplexRestriction_extend X L _

end TopCat.Sheaf
