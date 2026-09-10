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

public import FormalConjecturesForMathlib.AlgebraicGeometry.BettiGlobalSectionsComparison
public import FormalConjecturesForMathlib.AlgebraicTopology.GlobalSingularRestriction
public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeCochainCone

/-!
# Global singular restriction and relative cohomology

This file identifies restriction on global raw singular cochains with the algebraic dual of
the singular-chain inclusion of a topological pair.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

universe u v

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private lemma mapExtendIso_inv_naturality
    {C D : Type u} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D]
    {i i' : Type v} {c : ComplexShape i} {c' : ComplexShape i'}
    (F : Functor C D) [F.Additive] (K L : HomologicalComplex C c) (f : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] :
    HomologicalComplex.extendMap
          ((F.mapHomologicalComplex c).map f) e ≫
        (HomologicalComplex.mapExtendIso F L e).inv =
      (HomologicalComplex.mapExtendIso F K e).inv ≫
        (F.mapHomologicalComplex c').map (HomologicalComplex.extendMap f e) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change HomologicalComplex.extend.mapX
        ((F.mapHomologicalComplex c).map f) (e.r q) ≫
      (HomologicalComplex.mapExtendXIsoAux F L (e.r q)).inv =
    (HomologicalComplex.mapExtendXIsoAux F K (e.r q)).inv ≫
      F.map (HomologicalComplex.extend.mapX f (e.r q))
  generalize e.r q = x
  cases x with
  | none =>
      dsimp [HomologicalComplex.extend.mapX, HomologicalComplex.mapExtendXIsoAux]
      simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  | some n =>
      dsimp [HomologicalComplex.extend.mapX, HomologicalComplex.mapExtendXIsoAux]
      change F.map (f.f n) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (f.f n)
      rw [Category.comp_id, Category.id_comp]

variable (R : Type) [Field R] (X : TopCat.{0})

/-- Raw global singular cochains, transported from top-open cochains to ordinary singular
cochains and with their scalar structure forgotten. -/
def globalRawSingularCochainComplexIsoSingular :
    globalRawSingularCochainComplex R X ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R X).linearDualCochainComplex :=
  globalRawSingularCochainComplexIso R X ≪≫
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapIso (singularCochainComplexIsoTopOpen R X).symm

/-- The raw global pushforward from a subset, transported to ordinary singular cochains on
that subset. -/
def globalRawPushforwardSingularCochainComplexIsoSingular (A : Set X) :
    globalRawPushforwardSingularCochainComplex R
        (topologicalSubsetInclusion X A) ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R (TopCat.of A)).linearDualCochainComplex :=
  globalRawSingularCochainComplexIsoSingular R (TopCat.of A)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction between the inverse-image top opens becomes the original continuous map after
identifying both top opens with their ambient spaces. -/
lemma topOpenPreimageChainMap_transport {U : TopCat.{0}} (j : U ⟶ X) :
    (topOpenSingularChainComplexIso R U).inv ≫
        preimageOpenChainMap R j (⊤ : Opens X) ≫
      (topOpenSingularChainComplexIso R X).hom =
    ((singularChainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map j := by
  let F := (singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)
  change F.map (Opens.inclusionTopIso U).inv ≫
      F.map (preimageOpenToOpen j (⊤ : Opens X)) ≫
        F.map (Opens.inclusionTopIso X).hom = F.map j
  rw [← F.map_comp, ← F.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The chain map between top opens induced by a subset inclusion is conjugate to the chain map
of the associated topological pair. -/
lemma topOpenSubsetChainMap_transport (A : Set X) :
    (topOpenSingularChainComplexIso R (TopCat.of A)).inv ≫
        preimageOpenChainMap R (topologicalSubsetInclusion X A) (⊤ : Opens X) =
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom ≫
        (topOpenSingularChainComplexIso R X).inv := by
  change (topOpenSingularChainComplexIso R (TopCat.of A)).inv ≫
        preimageOpenChainMap R (topologicalSubsetInclusion X A) (⊤ : Opens X) =
      ((singularChainComplexFunctor (ModuleCat R)).obj
          (ModuleCat.of R R)).map (topologicalSubsetInclusion X A) ≫
        (topOpenSingularChainComplexIso R X).inv
  apply (cancel_mono (topOpenSingularChainComplexIso R X).hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    topOpenPreimageChainMap_transport R X (topologicalSubsetInclusion X A)

set_option backward.isDefEq.respectTransparency false in
/-- Under the top-open identifications, raw global restriction is the dual of the singular-chain
inclusion of the corresponding topological pair. -/
lemma globalRawSingularRestriction_transport (A : Set X) :
    globalRawSingularRestriction R (topologicalSubsetInclusion X A) ≫
        (globalRawPushforwardSingularCochainComplexIsoSingular R X A).hom =
      (globalRawSingularCochainComplexIsoSingular R X).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (HomologicalComplex.linearDualMap
              ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains R X (.op (⊤ : Opens X)) n at φ
  apply LinearMap.ext
  intro c
  change φ
      (((((topOpenSingularChainComplexIso R (TopCat.of A)).inv ≫
        preimageOpenChainMap R (topologicalSubsetInclusion X A) (⊤ : Opens X)).f n).hom) c) =
    φ ((((((chainPairFunctor R).obj (TopPair.ofSubset A)).hom ≫
      (topOpenSingularChainComplexIso R X).inv).f n).hom) c)
  exact congrArg φ (ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f n) (topOpenSubsetChainMap_transport R X A)) c)

/-- The raw global singular-cochain complex, extended by zero to integer degrees. -/
def globalRawSingularCochainComplexInt : CochainComplex AddCommGrpCat ℤ :=
  (globalRawSingularCochainComplex R X).extend ComplexShape.embeddingUpNat

/-- The raw global singular-cochain pushforward from a subset, extended by zero to integer
degrees. -/
def globalRawPushforwardSingularCochainComplexInt (A : Set X) :
    CochainComplex AddCommGrpCat ℤ :=
  (globalRawPushforwardSingularCochainComplex R
    (topologicalSubsetInclusion X A)).extend ComplexShape.embeddingUpNat

/-- Raw global restriction, extended by zero to integer degrees. -/
def globalRawSingularRestrictionInt (A : Set X) :
    globalRawSingularCochainComplexInt R X ⟶
      globalRawPushforwardSingularCochainComplexInt R X A :=
  HomologicalComplex.extendMap
    (globalRawSingularRestriction R (topologicalSubsetInclusion X A))
      ComplexShape.embeddingUpNat

/-- The integer extension of raw ambient global cochains is isomorphic to the integer extension
of the forgotten ordinary singular-cochain complex. -/
def globalRawSingularCochainComplexIntIsoSingular :
    globalRawSingularCochainComplexInt R X ≅
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R X).linearDualCochainComplex).extend
            ComplexShape.embeddingUpNat :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
    (globalRawSingularCochainComplexIsoSingular R X)

/-- The integer extension of the raw pushforward from a subset is isomorphic to the integer
extension of forgotten ordinary singular cochains on that subset. -/
def globalRawPushforwardSingularCochainComplexIntIsoSingular (A : Set X) :
    globalRawPushforwardSingularCochainComplexInt R X A ≅
      (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (SingularChainComplex R (TopCat.of A)).linearDualCochainComplex).extend
            ComplexShape.embeddingUpNat :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).mapIso
    (globalRawPushforwardSingularCochainComplexIsoSingular R X A)

set_option backward.isDefEq.respectTransparency false in
/-- Integer-extended raw restriction is conjugate to the integer extension of the forgotten
dual singular-chain inclusion. -/
lemma globalRawSingularRestrictionInt_transport (A : Set X) :
    globalRawSingularRestrictionInt R X A ≫
        (globalRawPushforwardSingularCochainComplexIntIsoSingular R X A).hom =
      (globalRawSingularCochainComplexIntIsoSingular R X).hom ≫
        HomologicalComplex.extendMap
          (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
            (ComplexShape.up ℕ)).map
              (HomologicalComplex.linearDualMap
                ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom))
          ComplexShape.embeddingUpNat := by
  change (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
      (globalRawSingularRestriction R (topologicalSubsetInclusion X A)) ≫
        (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
          (globalRawPushforwardSingularCochainComplexIsoSingular R X A).hom =
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
        (globalRawSingularCochainComplexIsoSingular R X).hom ≫
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat).map
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (HomologicalComplex.linearDualMap
              ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom))
  rw [← Functor.map_comp, globalRawSingularRestriction_transport, Functor.map_comp]

/-- Raw ambient global cochains, transported all the way to the forgotten integer-indexed
singular-cochain complex used by relative cohomology. -/
def globalRawSingularCochainComplexIntIsoRelative :
    globalRawSingularCochainComplexInt R X ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((SingularChainComplex R X).linearDualCochainComplex.extend
            ComplexShape.embeddingUpNat) :=
  globalRawSingularCochainComplexIntIsoSingular R X ≪≫
    (HomologicalComplex.mapExtendIso
      (forget₂ (ModuleCat R) AddCommGrpCat)
      (SingularChainComplex R X).linearDualCochainComplex
      ComplexShape.embeddingUpNat).symm

/-- Raw global cochains on a subset, transported all the way to the forgotten integer-indexed
singular-cochain complex used by relative cohomology. -/
def globalRawPushforwardSingularCochainComplexIntIsoRelative (A : Set X) :
    globalRawPushforwardSingularCochainComplexInt R X A ≅
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((SingularChainComplex R (TopCat.of A)).linearDualCochainComplex.extend
            ComplexShape.embeddingUpNat) :=
  globalRawPushforwardSingularCochainComplexIntIsoSingular R X A ≪≫
    (HomologicalComplex.mapExtendIso
      (forget₂ (ModuleCat R) AddCommGrpCat)
      (SingularChainComplex R (TopCat.of A)).linearDualCochainComplex
      ComplexShape.embeddingUpNat).symm

set_option backward.isDefEq.respectTransparency false in
/-- Integer-extended raw restriction is exactly the forgotten relative singular-cochain
restriction after transporting both source and target. -/
lemma globalRawSingularRestrictionInt_transport_relative (A : Set X) :
    globalRawSingularRestrictionInt R X A ≫
        (globalRawPushforwardSingularCochainComplexIntIsoRelative R X A).hom =
      (globalRawSingularCochainComplexIntIsoRelative R X).hom ≫
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (relativeCochainRestrictionInt R (TopPair.ofSubset A)) := by
  change globalRawSingularRestrictionInt R X A ≫
        ((globalRawPushforwardSingularCochainComplexIntIsoSingular R X A).hom ≫
          (HomologicalComplex.mapExtendIso
            (forget₂ (ModuleCat R) AddCommGrpCat)
            (SingularChainComplex R (TopCat.of A)).linearDualCochainComplex
            ComplexShape.embeddingUpNat).inv) =
    ((globalRawSingularCochainComplexIntIsoSingular R X).hom ≫
        (HomologicalComplex.mapExtendIso
          (forget₂ (ModuleCat R) AddCommGrpCat)
          (SingularChainComplex R X).linearDualCochainComplex
          ComplexShape.embeddingUpNat).inv) ≫
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (relativeCochainRestrictionInt R (TopPair.ofSubset A))
  rw [← Category.assoc, globalRawSingularRestrictionInt_transport]
  simp only [Category.assoc]
  apply (cancel_epi
    (globalRawSingularCochainComplexIntIsoSingular R X).hom).2
  exact mapExtendIso_inv_naturality
    (forget₂ (ModuleCat R) AddCommGrpCat)
    (SingularChainComplex R X).linearDualCochainComplex
    (SingularChainComplex R (TopCat.of A)).linearDualCochainComplex
    (HomologicalComplex.linearDualMap
      ((chainPairFunctor R).obj (TopPair.ofSubset A)).hom)
    ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The mapping cone of raw global restriction is isomorphic to the mapping cone of the
forgotten relative singular-cochain restriction. -/
def globalRawSingularRestrictionConeIsoRelative (A : Set X) :
    CochainComplex.mappingCone (globalRawSingularRestrictionInt R X A) ≅
      CochainComplex.mappingCone
        (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (relativeCochainRestrictionInt R (TopPair.ofSubset A))) := by
  let eX := globalRawSingularCochainComplexIntIsoRelative R X
  let eA := globalRawPushforwardSingularCochainComplexIntIsoRelative R X A
  let f := globalRawSingularRestrictionInt R X A
  let g := ((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      (relativeCochainRestrictionInt R (TopPair.ofSubset A))
  have h : f ≫ eA.hom = eX.hom ≫ g :=
    globalRawSingularRestrictionInt_transport_relative R X A
  exact HomologicalComplex.homotopyCofiber.mapArrowIso f g
    (fun j ↦ ⟨j - 1, ComplexShape.up_mk _ _ (by lia)⟩)
    (Arrow.isoMk eX eA h.symm)

/-- The cohomology of the raw global restriction cone computes relative singular cohomology.
The mapping-cone degree is one below the relative cohomological degree. -/
def globalRawSingularRestrictionConeCohomologyEquivRelative
    (A : Set X) (n : ℕ) :
    (CochainComplex.mappingCone
      (globalRawSingularRestrictionInt R X A)).homology ((n : ℤ) - 1) ≃+
        RelativeCohomology R (TopPair.ofSubset A) n :=
  (HomologicalComplex.homologyMapIso
      (globalRawSingularRestrictionConeIsoRelative R X A) ((n : ℤ) - 1))
    |>.addCommGroupIsoToAddEquiv |>.trans <|
  (HomologicalComplex.homologyMapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso
        (relativeCochainRestrictionInt R (TopPair.ofSubset A))
        (forget₂ (ModuleCat R) AddCommGrpCat)).symm ((n : ℤ) - 1))
    |>.addCommGroupIsoToAddEquiv |>.trans <|
  (ShortComplex.mapHomologyIso
      ((CochainComplex.mappingCone
        (relativeCochainRestrictionInt R (TopPair.ofSubset A))).sc ((n : ℤ) - 1))
      (forget₂ (ModuleCat R) AddCommGrpCat))
    |>.addCommGroupIsoToAddEquiv |>.trans <|
  (relativeCochainConeCohomologyEquiv R (TopPair.ofSubset A) n).toAddEquiv

/-- The raw global restriction cone for the complement of a support computes singular
cohomology with that support. -/
def globalRawSingularRestrictionConeCohomologyEquivSupport
    (Z : Set X) (n : ℕ) :
    (CochainComplex.mappingCone
      (globalRawSingularRestrictionInt R X Zᶜ)).homology ((n : ℤ) - 1) ≃+
        CohomologyWithSupport R X Z n :=
  globalRawSingularRestrictionConeCohomologyEquivRelative R X Zᶜ n

end AlgebraicTopology.Singular
