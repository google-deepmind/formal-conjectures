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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.OpenSheafRestriction
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiCohomologyWithSupportComparison
public import FormalConjecturesForMathlib.Definitions.AlgebraicGeometry.BettiSupportSingularHypercohomologyComparison

/-!
# Comparing an ambient resolution with a resolution on an open subspace

The comparison is lifted on the open subspace across the actual restricted
augmentation. Exact open restriction and the normalized constant-sheaf
comparison prove that this augmentation is a monic quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

omit [EnoughInjectives C] in
lemma injective_extend_nat (I : CochainComplex C ℕ) (hI : ∀ n, Injective (I.X n))
    (q : ℤ) : Injective ((I.extend ComplexShape.embeddingUpNat).X q) := by
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    exact Injective.of_iso (I.extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm (hI n)
  · exact (I.isZero_extend_X ComplexShape.embeddingUpNat q (fun n hn => hq ⟨n, hn⟩)).injective

omit [EnoughInjectives C] in
lemma mono_extendMap_nat {K L : CochainComplex C ℕ} (a : K ⟶ L) [Mono a] :
    Mono (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat) := by
  apply HomologicalComplex.mono_of_mono_f
  intro q
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    rw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl]
    infer_instance
  · exact (K.isZero_extend_X ComplexShape.embeddingUpNat q (fun n hn => hq ⟨n, hn⟩)).mono _

variable {A K I : CochainComplex C ℕ} (a : A ⟶ K) [Mono a] [QuasiIso a]
  (r : A ⟶ I) (hI : ∀ n, Injective (I.X n))

/-- Strict injective lifting for nonnegative cochain complexes, transported
through the fully faithful extension to integer degrees. -/
def liftToInjectiveNat : K ⟶ I := by
  let := mono_extendMap_nat a
  let : CochainComplex.IsStrictlyGE (A.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (K.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let : CochainComplex.IsStrictlyGE (I.extend ComplexShape.embeddingUpNat) 0 := inferInstance
  let f := liftToInjective
      (A := A.extend ComplexShape.embeddingUpNat)
      (S := K.extend ComplexShape.embeddingUpNat)
      (I := I.extend ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap a ComplexShape.embeddingUpNat)
      (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat)
      (injective_extend_nat I hI)
  exact (ComplexShape.embeddingUpNat.extendFunctor C).preimage f

end CochainComplex

namespace TopCat.Sheaf

variable (X : TopCat.{0}) (U : Opens X) (A : AddCommGrpCat.{0})

/-- Constant coefficients with the topological-sheaf category displayed explicitly. -/
abbrev resolutionConstantSheaf (Y : TopCat.{0}) : Sheaf AddCommGrpCat.{0} Y :=
  (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A

set_option backward.isDefEq.respectTransparency false in
/-- The fixed ambient injective resolution of the constant coefficient sheaf. -/
def ambientConstantInjectiveResolution :
    InjectiveResolution (C := Sheaf AddCommGrpCat.{0} X)
      (resolutionConstantSheaf A X) :=
  injectiveResolution (C := Sheaf AddCommGrpCat.{0} X) _

set_option backward.isDefEq.respectTransparency false in
/-- The separately chosen injective resolution on the open subspace. -/
def openConstantInjectiveResolution :
    InjectiveResolution (C := Sheaf AddCommGrpCat.{0} (TopCat.of U))
      (resolutionConstantSheaf A (TopCat.of U)) :=
  injectiveResolution (C := Sheaf AddCommGrpCat.{0} (TopCat.of U)) _

/-- Restrict the ambient injective resolution termwise. It is flasque, but no
assertion that its terms are injective on the subspace is required. -/
def restrictedAmbientConstantResolution :
    CochainComplex (Sheaf AddCommGrpCat.{0} (TopCat.of U)) ℕ :=
  ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj
    (ambientConstantInjectiveResolution X A).cocomplex

/-- The augmentation from actual open constants into the restricted ambient
resolution, using the normalized constant/open isomorphism. -/
def restrictedAmbientConstantAugmentation :
    (CochainComplex.single₀ (Sheaf AddCommGrpCat.{0} (TopCat.of U))).obj
        ((constantSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat).obj A) ⟶
      restrictedAmbientConstantResolution X U A :=
  (CochainComplex.single₀ _).map (constantOpenSheafRestrictionIso X U A).hom ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat) (.up ℕ) 0).inv.app _ ≫
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
      (ambientConstantInjectiveResolution X A).ι

set_option backward.isDefEq.respectTransparency false in
instance restrictedAmbientConstantAugmentation_mono :
    Mono (restrictedAmbientConstantAugmentation X U A) := by
  let : Mono (ambientConstantInjectiveResolution X A).ι :=
    HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)
  dsimp only [restrictedAmbientConstantAugmentation]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance restrictedAmbientConstantAugmentation_quasiIso :
    QuasiIso (restrictedAmbientConstantAugmentation X U A) := by
  let : QuasiIso (ambientConstantInjectiveResolution X A).ι :=
    (ambientConstantInjectiveResolution X A).quasiIso
  have : QuasiIso
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map
        (ambientConstantInjectiveResolution X A).ι) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  dsimp only [restrictedAmbientConstantAugmentation]
  infer_instance

/-- An actual map from the restricted ambient resolution to the independent
open-subspace resolution, extending the prescribed constant augmentation. -/
def restrictedAmbientToOpenResolution :
    restrictedAmbientConstantResolution X U A ⟶
      (openConstantInjectiveResolution X U A).cocomplex :=
  CochainComplex.liftToInjectiveNat (restrictedAmbientConstantAugmentation X U A)
    (openConstantInjectiveResolution X U A).ι
      (fun n => (openConstantInjectiveResolution X U A).injective n)

instance restrictedAmbientConstantResolution_isFlasque (n : ℕ) :
    ((restrictedAmbientConstantResolution X U A).X n).IsFlasque := by
  change ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
    ((ambientConstantInjectiveResolution X A).cocomplex.X n)).IsFlasque
  let : IsFlasque ((ambientConstantInjectiveResolution X A).cocomplex.X n) :=
    @injective_isFlasque _ _ ((ambientConstantInjectiveResolution X A).injective n)
  exact openSheafRestriction_isFlasque X U _

/-- The actual restriction of the ambient injective complex. -/
def ambientInjectiveRestriction :
    (ambientConstantInjectiveResolution X A).cocomplex ⟶
      ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
        (restrictedAmbientConstantResolution X U A) where
  f n := (toOpenRestrictionPushforward X U).app
    ((ambientConstantInjectiveResolution X A).cocomplex.X n)
  comm' i j _h := ((toOpenRestrictionPushforward X U).naturality
    ((ambientConstantInjectiveResolution X A).cocomplex.d i j)).symm

/-- Restriction from the ambient injective resolution to the independently
chosen open-subspace resolution, through actual open restriction. -/
def ambientToOpenInjectiveResolution :
    (ambientConstantInjectiveResolution X A).cocomplex ⟶
      ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
        (openConstantInjectiveResolution X U A).cocomplex :=
  ambientInjectiveRestriction X U A ≫
    ((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
      (restrictedAmbientToOpenResolution X U A)

/-- Global sections of the pushed-forward comparison. Its source uses the
actual open restriction of the ambient resolution, not a supplied model. -/
def globalRestrictedAmbientToOpenResolution :
    ((IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).obj
        (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
          (restrictedAmbientConstantResolution X U A)) ⟶
    ((IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).obj
        (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).obj
          (openConstantInjectiveResolution X U A).cocomplex) :=
  ((IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
    (.up ℕ)).map
      (((pushforward AddCommGrpCat U.inclusion').mapHomologicalComplex (.up ℕ)).map
        (restrictedAmbientToOpenResolution X U A))

end TopCat.Sheaf
