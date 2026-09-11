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

public import FormalConjecturesForMathlib.AlgebraicTopology.RelativeCochainCone
public import FormalConjecturesForMathlib.AlgebraicTopology.LinearDualHomologyNaturality
public import FormalConjecturesForMathlib.Algebra.Homology.DerivedCategory.MappingCoconeShortExactNaturality

/-! # Canonical natural relative-cochain cone comparison

Unlike a completion of a morphism of distinguished triangles, the explicit
short-exact-sequence lift is natural before passage to homology.

The lift is positive `(inclusion, 0)`; Mathlib's cone connecting morphism
is the negative first projection. Their exact composite is displayed below.
This file does not assert equality with the older
`relativeCochainConeCohomologyEquiv`, which uses a completed triangle map.
Such equality, in particular on normalized point neighborhoods, is a
separate comparison theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual contravariant map of dual relative short exact sequences. -/
def relativeDualCochainShortComplexNatMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    relativeDualCochainShortComplexNat R Y ⟶ relativeDualCochainShortComplexNat R X where
  τ₁ := HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f)
  τ₂ := HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).right
  τ₃ := HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).left
  comm₁₂ := by
    change HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f) ≫
        HomologicalComplex.linearDualMap (relativeChainProjection R X) =
      HomologicalComplex.linearDualMap (relativeChainProjection R Y) ≫
        HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).right
    rw [← HomologicalComplex.linearDualMap_comp, ← HomologicalComplex.linearDualMap_comp]
    exact congrArg HomologicalComplex.linearDualMap
      ((coker.π (C := ChainCategory R)).naturality ((chainPairFunctor R).map f)).symm
  comm₂₃ := by
    change HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).right ≫
        HomologicalComplex.linearDualMap ((chainPairFunctor R).obj X).hom =
      HomologicalComplex.linearDualMap ((chainPairFunctor R).obj Y).hom ≫
        HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).left
    rw [← HomologicalComplex.linearDualMap_comp, ← HomologicalComplex.linearDualMap_comp]
    exact congrArg HomologicalComplex.linearDualMap ((chainPairFunctor R).map f).w.symm

/-- Extend the actual relative short-complex map to integer degrees. -/
def relativeDualCochainShortComplexIntMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    relativeDualCochainShortComplexInt R Y ⟶ relativeDualCochainShortComplexInt R X :=
  ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R)).mapShortComplex).map
    (relativeDualCochainShortComplexNatMap R f)

/-- The literal relative restriction-cone map induced by a map of pairs. -/
def relativeCochainConeMap {X Y : TopPair.{u}} (f : X ⟶ Y) :
    CochainComplex.mappingCone (relativeCochainRestrictionInt R Y) ⟶
      CochainComplex.mappingCone (relativeCochainRestrictionInt R X) :=
  CochainComplex.mappingCone.map _ _
    (relativeDualCochainShortComplexIntMap R f).τ₂
    (relativeDualCochainShortComplexIntMap R f).τ₃
    (relativeDualCochainShortComplexIntMap R f).comm₂₃.symm

/-- Canonical comparison from integer dual-relative cohomology to its
restriction cone, induced by the positive `(inclusion, 0)` lift. -/
def relativeDualCochainHomologyIsoCone (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≅
      (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone
    (relativeDualCochainShortComplexInt R X)
    (relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

/-- Exact sign normalization of the canonical relative-to-cone map. -/
@[reassoc]
lemma relativeDualCochainLift_connecting (X : TopPair.{u}) :
    CochainComplex.mappingCocone.shiftedLiftShortComplex
        (relativeDualCochainShortComplexInt R X) ≫
      (CochainComplex.mappingCone.triangle (relativeCochainRestrictionInt R X)).mor₃ =
    -(relativeDualCochainShortComplexInt R X).f⟦(1 : ℤ)⟧' :=
  CochainComplex.mappingCocone.shiftedLiftShortComplex_connecting _

/-- Actual integer dual-relative cohomology computes the repository's
relative cohomology by the evaluation pairing. -/
def relativeDualCochainCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) ≃ₗ[R]
      RelativeCohomology R X n :=
  (((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv.trans
      (HomologicalComplex.linearDualHomologyEquiv ((relativeChainFunctor R).obj X) n)

/-- Relative cohomology computed from the explicit canonical cone lift.
No arbitrary completion of a triangle map enters this equivalence. -/
def relativeCochainConeCohomologyEquivCanonical (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R] RelativeCohomology R X n :=
  (relativeDualCochainHomologyIsoCone R X n).symm.toLinearEquiv.trans
    (relativeDualCochainCohomologyEquiv R X n)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical relative dual-to-cone comparison is natural. -/
@[reassoc]
lemma relativeDualCochainHomologyIsoCone_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n ≫
      (relativeDualCochainHomologyIsoCone R X n).hom =
    (relativeDualCochainHomologyIsoCone R Y n).hom ≫
      HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1) :=
  CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality
    (relativeDualCochainShortComplexIntMap R f)
    (relativeDualCochainShortComplexInt_shortExact R Y)
    (relativeDualCochainShortComplexInt_shortExact R X) ((n : ℤ) - 1) n (by omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Integer extension and universal coefficients preserve the actual
relative pullback map. -/
lemma relativeDualCochainCohomologyEquiv_naturality {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : (relativeDualCochainShortComplexInt R Y).X₁.homology (n : ℤ)) :
    relativeDualCochainCohomologyEquiv R X n
        (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n a) =
      relativeCohomologyMap R n f (relativeDualCochainCohomologyEquiv R Y n a) := by
  have h := HomologicalComplex.extendHomologyIso_hom_naturality
    (HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f))
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have ha := ConcreteCategory.congr_hom h a
  ext z
  change HomologicalComplex.linearDualHomologyEquiv ((relativeChainFunctor R).obj X) n
    ((((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
      (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n a)) z = _
  rw [show (((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom
      (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n a) =
    HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap ((relativeChainFunctor R).map f)) n
      ((((relativeChainFunctor R).obj Y).linearDualCochainComplex.extendHomologyIso
        ComplexShape.embeddingUpNat rfl).hom a) from ha]
  exact HomologicalComplex.linearDualHomologyEquiv_naturality _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical restriction-cone comparison intertwines actual maps of
pairs with the existing relative cohomology pullback. -/
lemma relativeCochainConeCohomologyEquivCanonical_naturality
    {X Y : TopPair.{u}} (f : X ⟶ Y) (n : ℕ)
    (a : (CochainComplex.mappingCone (relativeCochainRestrictionInt R Y)).homology
      ((n : ℤ) - 1)) :
    relativeCochainConeCohomologyEquivCanonical R X n
        (HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1) a) =
      relativeCohomologyMap R n f (relativeCochainConeCohomologyEquivCanonical R Y n a) := by
  obtain ⟨b, rfl⟩ := (relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv.surjective a
  change relativeCochainConeCohomologyEquivCanonical R X n
      (HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1)
        ((relativeDualCochainHomologyIsoCone R Y n).hom b)) =
    relativeCohomologyMap R n f (relativeCochainConeCohomologyEquivCanonical R Y n
      ((relativeDualCochainHomologyIsoCone R Y n).hom b))
  have h := ConcreteCategory.congr_hom (relativeDualCochainHomologyIsoCone_naturality R f n) b
  change (relativeDualCochainHomologyIsoCone R X n).hom
      (HomologicalComplex.homologyMap (relativeDualCochainShortComplexIntMap R f).τ₁ n b) =
    HomologicalComplex.homologyMap (relativeCochainConeMap R f) ((n : ℤ) - 1)
      ((relativeDualCochainHomologyIsoCone R Y n).hom b) at h
  rw [← h]
  change relativeDualCochainCohomologyEquiv R X n
      ((relativeDualCochainHomologyIsoCone R X n).toLinearEquiv.symm
        ((relativeDualCochainHomologyIsoCone R X n).toLinearEquiv _)) =
    relativeCohomologyMap R n f (relativeDualCochainCohomologyEquiv R Y n
      ((relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv.symm
        ((relativeDualCochainHomologyIsoCone R Y n).toLinearEquiv b)))
  simp only [LinearEquiv.symm_apply_apply]
  exact relativeDualCochainCohomologyEquiv_naturality R f n b

end AlgebraicTopology.Singular
