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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.CohomologyWithSupport
public import FormalConjecturesForMathlib.Lemmas.AlgebraicGeometry.BettiSheafComparison
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.MappingConeQuasiIso
public import Mathlib.Algebra.Homology.ModelCategory.Injective

/-!
# Betti comparison with support

This file proves the categorical input needed to replace the constant-sheaf term in the
mapping-cone model for supported cohomology by a singular-cochain resolution. In particular,
direct image along an open embedding preserves injective additive sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace HomotopicalAlgebra
open scoped CochainComplex.Plus.modelCategoryQuillen

namespace Topology.IsOpenEmbedding

variable {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : IsOpenEmbedding f)

set_option linter.style.haveILetI false in
/-- Naive pullback along an open embedding preserves monomorphisms of additive sheaves. -/
private lemma sheafPullback_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (hf.sheafPullback AddCommGrpCat.{0}) := by
  constructor
  intro F G g hg
  letI : Mono g := hg
  let : Mono g.hom := Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{0} Y) g
  let : Mono (Functor.whiskerLeft hf.functor.op g.hom) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    exact (NatTrans.mono_iff_mono_app g.hom).mp inferInstance _
  let : Mono ((hf.sheafPullback AddCommGrpCat.{0}).map g).hom := by
    change Mono (Functor.whiskerLeft hf.functor.op g.hom)
    infer_instance
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono
    (J := Opens.grothendieckTopology X) (A := AddCommGrpCat.{0})
      ((hf.sheafPullback AddCommGrpCat.{0}).map g)

set_option linter.style.haveILetI false in
/-- Sheaf pullback along an open embedding preserves monomorphisms. -/
private lemma pullback_preservesMonomorphisms (hf : IsOpenEmbedding f) :
    Functor.PreservesMonomorphisms (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := by
  letI := sheafPullback_preservesMonomorphisms hf
  exact Functor.PreservesMonomorphisms.of_iso
    (hf.sheafPullbackIso AddCommGrpCat.{0}).symm

set_option linter.style.haveILetI false in
/-- Direct image along an open embedding preserves injective additive sheaves. -/
private theorem pushforward_injective (hf : IsOpenEmbedding f)
    (I : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective I] :
    Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).obj I) := by
  letI := pullback_preservesMonomorphisms hf
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).map_injective I
    inferInstance

end Topology.IsOpenEmbedding

namespace CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

section

variable {A S I : CochainComplex C ℤ}
  [A.IsStrictlyGE 0] [S.IsStrictlyGE 0] [I.IsStrictlyGE 0]
  (a : A ⟶ S) [Mono a] [QuasiIso a]
  (r : A ⟶ I)

/-- A map into a bounded-below degreewise-injective complex extends strictly across a monic
quasi-isomorphism. This is the lifting property in the injective model structure. -/
noncomputable def liftToInjective (hI : ∀ n : ℤ, Injective (I.X n)) : S ⟶ I := by
  let A' : Plus C := ⟨A, 0, inferInstance⟩
  let S' : Plus C := ⟨S, 0, inferInstance⟩
  let I' : Plus C := ⟨I, 0, inferInstance⟩
  let a' : A' ⟶ S' := ObjectProperty.homMk a
  let r' : A' ⟶ I' := ObjectProperty.homMk r
  let Z' := ⊤_ Plus C
  let p : I' ⟶ Z' := terminal.from I'
  let b : S' ⟶ Z' := terminal.from S'
  let sq : CommSq r' a' p b := CommSq.mk (Subsingleton.elim _ _)
  letI : Mono a' := (Plus.mono_iff a').2 (inferInstance : Mono a)
  letI : WeakEquivalence a' :=
    (Plus.modelCategoryQuillen.weakEquivalence_iff a').2 (inferInstance : QuasiIso a)
  letI : IsFibrant I' :=
    (Plus.modelCategoryQuillen.isFibrant_iff I').2 hI
  exact sq.lift.hom

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
set_option linter.unusedSectionVars false in
/-- The injective lift strictly extends the prescribed map. -/
lemma comp_liftToInjective (hI : ∀ n : ℤ, Injective (I.X n)) :
    a ≫ liftToInjective a r hI = r := by
  let A' : Plus C := ⟨A, 0, inferInstance⟩
  let S' : Plus C := ⟨S, 0, inferInstance⟩
  let I' : Plus C := ⟨I, 0, inferInstance⟩
  let a' : A' ⟶ S' := ObjectProperty.homMk a
  let r' : A' ⟶ I' := ObjectProperty.homMk r
  let Z' := ⊤_ Plus C
  let p : I' ⟶ Z' := terminal.from I'
  let b : S' ⟶ Z' := terminal.from S'
  let sq : CommSq r' a' p b := CommSq.mk (Subsingleton.elim _ _)
  letI : Mono a' := (Plus.mono_iff a').2 (inferInstance : Mono a)
  letI : WeakEquivalence a' :=
    (Plus.modelCategoryQuillen.weakEquivalence_iff a').2 (inferInstance : QuasiIso a)
  letI : IsFibrant I' :=
    (Plus.modelCategoryQuillen.isFibrant_iff I').2 hI
  exact congrArg (fun f ↦ f.hom) sq.fac_left

/-- Replacing the source of a restriction map by a monic quasi-isomorphic resolution induces a
quasi-isomorphism of mapping cones. -/
def sourceReplacementConeMap (hI : ∀ n : ℤ, Injective (I.X n)) :
    mappingCone r ⟶ mappingCone (liftToInjective a r hI) :=
  mappingCone.map r (liftToInjective a r hI) a (𝟙 I)
    (by rw [Category.comp_id, comp_liftToInjective])

noncomputable instance sourceReplacementConeMap_quasiIso
    [HasDerivedCategory C]
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    QuasiIso (sourceReplacementConeMap a r hI) :=
  mappingCone.map_quasiIso_of_vertical_quasiIso r (liftToInjective a r hI)
    a (𝟙 I) (by rw [Category.comp_id, comp_liftToInjective])

end

end CochainComplex

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false in
/-- The constant-to-singular-cochain resolution is a monomorphism of complexes. -/
lemma constantsToSingularCochainSheafComplex_mono
    (R : Type) [Field R] (Y : TopCat.{0}) :
    Mono (constantsToSingularCochainSheafComplex R Y) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  cases n with
  | zero =>
      change Mono (constantsToSingularCochainZeroSheaf R Y)
      exact constantsToSingularCochainZeroSheaf_mono R Y
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (constantCoefficientSheaf R Y) (n + 1) (by lia)).mono _

/-- Extending the constant-to-singular-cochain resolution to integer degrees remains monic. -/
lemma constantsToSingularCochainComplexInt_mono
    (R : Type) [Field R] (Y : TopCat.{0}) :
    Mono (HomologicalComplex.extendMap
      (constantsToSingularCochainSheafComplex R Y) ComplexShape.embeddingUpNat) := by
  let a := constantsToSingularCochainSheafComplex R Y
  let : Mono a := constantsToSingularCochainSheafComplex_mono R Y
  apply HomologicalComplex.mono_of_mono_f
  intro n
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    change Mono ((HomologicalComplex.extendMap a ComplexShape.embeddingUpNat).f (m : ℤ))
    rw [HomologicalComplex.extendMap_f a ComplexShape.embeddingUpNat
      (i := m) (i' := (m : ℤ)) rfl]
    infer_instance
  · exact (((CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat Y)).obj
      (constantCoefficientSheaf R Y)).isZero_extend_X
        ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩)).mono _

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

/-- The inclusion of the complement of a closed support is an open embedding. -/
lemma analyticComplementInclusion_isOpenEmbedding
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    Topology.IsOpenEmbedding (analyticComplementInclusion X Z) := by
  change Topology.IsOpenEmbedding
    (Subtype.val : (Zᶜ : Set (ComplexPoint X)) → ComplexPoint X)
  exact hZ.isOpen_compl.isOpenEmbedding_subtypeVal

/-- Every term of the chosen derived-pushforward model from an open complement is injective. -/
theorem derivedPushforwardComplementConstantRationalComplexInt_injective
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) (n : ℤ) :
    Injective ((derivedPushforwardComplementConstantRationalComplexInt X Z).X n) := by
  by_cases hn : ∃ m : ℕ, (m : ℤ) = n
  · obtain ⟨m, rfl⟩ := hn
    let e := (derivedPushforwardComplementConstantRationalComplexNat X Z).extendXIso
      ComplexShape.embeddingUpNat (i := m) rfl
    apply Injective.of_iso e.symm
    change Injective ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).obj
        ((complementConstantRationalInjectiveResolution X Z).cocomplex.X m))
    exact (analyticComplementInclusion_isOpenEmbedding X Z hZ).pushforward_injective _
  · exact (derivedPushforwardComplementConstantRationalComplexNat X Z).isZero_extend_X
      ComplexShape.embeddingUpNat n (fun i hi ↦ hn ⟨i, hi⟩) |>.injective

/-- The rational constant-to-singular comparison is a monomorphism of integer-indexed sheaf
complexes. -/
lemma rationalToSingularCochainComplexInt_mono :
    Mono (rationalToSingularCochainComplexInt X) := by
  change Mono (HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ
      (TopCat.of (ComplexPoint X))) ComplexShape.embeddingUpNat)
  exact AlgebraicTopology.Singular.constantsToSingularCochainComplexInt_mono ℚ _

variable [IsIntegral X.left] [Smooth X.hom]

local instance bettiSupportComparisonHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- A strict chain-level extension of restriction from rational constants to the chosen derived
pushforward complex across the singular-cochain resolution. -/
def singularResolutionRestriction
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    singularCochainSheafComplexInt X ℚ ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z := by
  let : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
    unfold constantFieldSheafComplexInt
    infer_instance
  let : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
    unfold singularCochainSheafComplexInt
    infer_instance
  let : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE
      0 := by
    unfold derivedPushforwardComplementConstantRationalComplexInt
    infer_instance
  let : Mono (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_mono X
  let : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  exact CochainComplex.liftToInjective
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

/-- Replacing rational constants by their singular-cochain resolution gives a quasi-isomorphic
mapping-cone model for supported cohomology. -/
def rationalSupportConeToSingularResolutionCone
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    rationalCohomologyWithSupportComplex X Z ⟶
      CochainComplex.mappingCone (singularResolutionRestriction X Z hZ) := by
  let : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
    unfold constantFieldSheafComplexInt
    infer_instance
  let : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
    unfold singularCochainSheafComplexInt
    infer_instance
  let : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE
      0 := by
    unfold derivedPushforwardComplementConstantRationalComplexInt
    infer_instance
  let : Mono (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_mono X
  let : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  exact CochainComplex.sourceReplacementConeMap
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ)

noncomputable instance rationalSupportConeToSingularResolutionCone_quasiIso
    (Z : Set (ComplexPoint X)) (hZ : IsClosed Z) :
    QuasiIso (rationalSupportConeToSingularResolutionCone X Z hZ) := by
  let : (constantFieldSheafComplexInt ℚ X).IsStrictlyGE 0 := by
    unfold constantFieldSheafComplexInt
    infer_instance
  let : (singularCochainSheafComplexInt X ℚ).IsStrictlyGE 0 := by
    unfold singularCochainSheafComplexInt
    infer_instance
  let : (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE
      0 := by
    unfold derivedPushforwardComplementConstantRationalComplexInt
    infer_instance
  let : Mono (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_mono X
  let : QuasiIso (rationalToSingularCochainComplexInt X) :=
    rationalToSingularCochainComplexInt_quasiIso X
  change QuasiIso (CochainComplex.sourceReplacementConeMap
    (rationalToSingularCochainComplexInt X)
    (rationalRestrictionComplexInt X Z)
    (derivedPushforwardComplementConstantRationalComplexInt_injective X Z hZ))
  infer_instance

end AlgebraicGeometry.ComplexPoint
