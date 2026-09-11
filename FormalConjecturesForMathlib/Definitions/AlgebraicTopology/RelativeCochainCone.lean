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

public import FormalConjecturesForMathlib.Mathlib.Algebra.Homology.DualExact
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Relative singular cohomology as a cochain mapping cone

For a topological pair `A ⊆ X`, restriction of singular cochains is the algebraic dual of
the inclusion `C_*(A) ⟶ C_*(X)`.  This file proves, without a finite-dimensionality
hypothesis, that the cohomology in degree `n - 1` of its mapping cone is the algebraic dual of
`H_n(X, A)`.

The proof dualizes the degreewise short exact sequence
`C_*(A) ⟶ C_*(X) ⟶ C_*(X, A)`, extends the resulting cochain complexes by zero to
integer degrees, and compares its rotated triangle with Mathlib's mapping-cone triangle.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- The short exact sequence of subspace, ambient, and relative singular chains. -/
def relativeChainShortComplex (X : TopPair.{u}) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk ((chainPairFunctor R).obj X).hom
    (relativeChainProjection R X)
    (subspaceChainMap_relativeChainProjection R X)

/-- The singular-chain map of a topological-pair inclusion is a monomorphism. -/
private lemma relativeChainMap_mono (X : TopPair.{u}) :
    Mono ((chainPairFunctor R).obj X).hom := by
  let : Mono X.hom :=
    (TopCat.mono_iff_injective X.hom).mpr X.prop.injective
  change Mono (((singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map X.hom)
  apply Functor.map_mono

/-- Singular chains of a pair form a short exact sequence. -/
private lemma relativeChainShortComplex_shortExact (X : TopPair.{u}) :
    (relativeChainShortComplex R X).ShortExact := by
  let : Mono ((chainPairFunctor R).obj X).hom := relativeChainMap_mono R X
  exact
    { exact := ShortComplex.exact_cokernel ((chainPairFunctor R).obj X).hom
      mono_f := by
        dsimp [relativeChainShortComplex]
        infer_instance
      epi_g := by
        dsimp [relativeChainShortComplex, relativeChainProjection]
        constructor
        intro Z g h w
        exact Cofork.IsColimit.hom_ext
          (cokernelIsCokernel ((chainPairFunctor R).obj X).hom) w }

set_option backward.isDefEq.respectTransparency false in
/-- The dual relative, ambient, and subspace cochain complexes in nonnegative degrees. -/
def relativeDualCochainShortComplexNat (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk
    (HomologicalComplex.linearDualMap (relativeChainProjection R X))
    (HomologicalComplex.linearDualMap ((chainPairFunctor R).obj X).hom)
    (by
      ext n φ
      change Module.Dual R (((relativeChainFunctor R).obj X).X n) at φ
      apply LinearMap.ext
      intro x
      change φ (((((chainPairFunctor R).obj X).hom ≫
        relativeChainProjection R X).f n).hom x) = 0
      rw [subspaceChainMap_relativeChainProjection]
      exact map_zero φ)

set_option backward.isDefEq.respectTransparency false in
/-- Dualizing the singular-chain sequence of a pair gives a short exact sequence of
nonnegative cochain complexes. -/
private lemma relativeDualCochainShortComplexNat_shortExact (X : TopPair.{u}) :
    (relativeDualCochainShortComplexNat R X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  let T := (relativeChainShortComplex R X).map
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
  have hT : T.ShortExact :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact
      (relativeChainShortComplex R X)).mp
        (relativeChainShortComplex_shortExact R X)) n
  apply ModuleCat.shortComplex_shortExact
  · dsimp [relativeDualCochainShortComplexNat, T]
    rw [LinearMap.exact_iff]
    exact (LinearMap.range_dualMap_eq_ker_dualMap_of_range_eq_ker
      T.f.hom T.g.hom hT.exact.moduleCat_range_eq_ker).symm
  · dsimp [relativeDualCochainShortComplexNat, T]
    change Function.Injective T.g.hom.dualMap
    exact LinearMap.dualMap_injective_of_surjective
      ((ModuleCat.epi_iff_surjective T.g).mp hT.epi_g)
  · dsimp [relativeDualCochainShortComplexNat, T]
    change Function.Surjective T.f.hom.dualMap
    exact LinearMap.dualMap_surjective_of_injective
      ((ModuleCat.mono_iff_injective T.f).mp hT.mono_f)

/-- The dual relative, ambient, and subspace cochain complexes, extended by zero to integer
degrees. -/
def relativeDualCochainShortComplexInt (X : TopPair.{u}) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (relativeDualCochainShortComplexNat R X).map
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))

/-- Restriction from ambient singular cochains to subspace singular cochains, in integer
degrees. -/
def relativeCochainRestrictionInt (X : TopPair.{u}) :
    ((SingularChainComplex R X.fst).linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat) ⟶
      (((chainPairFunctor R).obj X).left.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap
    (HomologicalComplex.linearDualMap ((chainPairFunctor R).obj X).hom)
    ComplexShape.embeddingUpNat

@[simp]
lemma relativeDualCochainShortComplexInt_g (X : TopPair.{u}) :
    (relativeDualCochainShortComplexInt R X).g = relativeCochainRestrictionInt R X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In a nonnegative degree, evaluation of the integer extension recovers evaluation of the
original nonnegative short complex. -/
def relativeDualCochainShortComplexIntEvalIso (X : TopPair.{u}) (n : ℕ) :
    (relativeDualCochainShortComplexInt R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (n : ℤ)) ≅
      (relativeDualCochainShortComplexNat R X).map
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n) := by
  have hn : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  refine ShortComplex.isoMk
    ((relativeDualCochainShortComplexNat R X).X₁.extendXIso
      ComplexShape.embeddingUpNat hn)
    ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
      ComplexShape.embeddingUpNat hn)
    ((relativeDualCochainShortComplexNat R X).X₃.extendXIso
      ComplexShape.embeddingUpNat hn)
    (by
      change ((relativeDualCochainShortComplexNat R X).X₁.extendXIso
          ComplexShape.embeddingUpNat hn).hom ≫
            (relativeDualCochainShortComplexNat R X).f.f n =
        (HomologicalComplex.extendMap
          (relativeDualCochainShortComplexNat R X).f
          ComplexShape.embeddingUpNat).f (n : ℤ) ≫
            ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
              ComplexShape.embeddingUpNat hn).hom
      rw [HomologicalComplex.extendMap_f _ _ hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by
      change ((relativeDualCochainShortComplexNat R X).X₂.extendXIso
          ComplexShape.embeddingUpNat hn).hom ≫
            (relativeDualCochainShortComplexNat R X).g.f n =
        (HomologicalComplex.extendMap
          (relativeDualCochainShortComplexNat R X).g
          ComplexShape.embeddingUpNat).f (n : ℤ) ≫
            ((relativeDualCochainShortComplexNat R X).X₃.extendXIso
              ComplexShape.embeddingUpNat hn).hom
      rw [HomologicalComplex.extendMap_f _ _ hn]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The integer-indexed dual cochain sequence of a pair is short exact. -/
lemma relativeDualCochainShortComplexInt_shortExact (X : TopPair.{u}) :
    (relativeDualCochainShortComplexInt R X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro z
  by_cases hz : 0 ≤ z
  · have hn : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz
    let e :
        (relativeDualCochainShortComplexNat R X).map
            (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) z.toNat) ≅
          (relativeDualCochainShortComplexInt R X).map
            (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) z) := by
      simpa only [hn] using
        (relativeDualCochainShortComplexIntEvalIso R X z.toNat).symm
    exact ShortComplex.shortExact_of_iso e
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact
        (relativeDualCochainShortComplexNat R X)).mp
          (relativeDualCochainShortComplexNat_shortExact R X)) z.toNat)
  · have hi : ∀ n : ℕ, ComplexShape.embeddingUpNat.f n ≠ z := by
      intro n hn
      apply hz
      rw [← hn]
      exact Int.natCast_nonneg n
    let S := (relativeDualCochainShortComplexInt R X).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) z)
    have h₁ : IsZero S.X₁ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₁.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    have h₂ : IsZero S.X₂ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₂.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    have h₃ : IsZero S.X₃ := by
      dsimp [S, relativeDualCochainShortComplexInt]
      exact (relativeDualCochainShortComplexNat R X).X₃.isZero_extend_X
        ComplexShape.embeddingUpNat z hi
    exact ShortComplex.Splitting.shortExact
      { r := 0
        s := 0
        f_r := h₁.eq_of_src _ _
        s_g := h₃.eq_of_tgt _ _
        id := h₂.eq_of_src _ _ }

/-- A degreewise splitting of the dual cochain sequence.  The choice is harmless: the final
cohomology comparison is independent of finite-dimensionality. -/
def relativeDualCochainDegreewiseSplitting (X : TopPair.{u}) (z : ℤ) :
    ((relativeDualCochainShortComplexInt R X).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) z)).Splitting :=
  (((HomologicalComplex.shortExact_iff_degreewise_shortExact
    (relativeDualCochainShortComplexInt R X)).mp
      (relativeDualCochainShortComplexInt_shortExact R X)) z).splittingOfProjective

/-- The triangle attached to the degreewise split dual cochain sequence is distinguished. -/
lemma relativeDualCochainTriangle_distinguished (X : TopPair.{u}) :
    CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X) ∈ distinguishedTriangles :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).mpr
    ⟨relativeDualCochainShortComplexInt R X,
      relativeDualCochainDegreewiseSplitting R X, ⟨Iso.refl _⟩⟩

/-- The rotated triangle of the dual short exact sequence agrees with the mapping-cone
triangle of singular-cochain restriction. -/
def relativeCochainConeTriangleIso (X : TopPair.{u}) :
    (CochainComplex.trianglehOfDegreewiseSplit
      (relativeDualCochainShortComplexInt R X)
      (relativeDualCochainDegreewiseSplitting R X)).rotate ≅
    CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X) :=
  isoTriangleOfIso₁₂
    (CochainComplex.trianglehOfDegreewiseSplit
      (relativeDualCochainShortComplexInt R X)
      (relativeDualCochainDegreewiseSplitting R X)).rotate
    (CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X))
    ((rotate_distinguished_triangle _).mp
      (relativeDualCochainTriangle_distinguished R X))
    (HomotopyCategory.mappingCone_triangleh_distinguished
      (relativeCochainRestrictionInt R X))
    (Iso.refl _) (Iso.refl _) (by
      change (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
          (relativeDualCochainShortComplexInt R X).g =
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
          (relativeCochainRestrictionInt R X)
      rw [relativeDualCochainShortComplexInt_g]
      rfl)

/-- The homotopy-category isomorphism from the shifted dual relative cochain complex to the
mapping cone of restriction. -/
def relativeDualShiftIsoCochainCone (X : TopPair.{u}) :
    (shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (1 : ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
          (relativeDualCochainShortComplexInt R X).X₁) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)) :=
  Pretriangulated.Triangle.π₃.mapIso (relativeCochainConeTriangleIso R X)

/-- Cohomology of the cochain restriction cone in degree `n - 1` is the cohomology in degree
`n` of the integer-indexed dual relative cochain complex. -/
def relativeCochainConeHomologyIsoDualRelativeInt (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≅
      (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let H (z : ℤ) := HomotopyCategory.homologyFunctor
    (ModuleCat.{u} R) (ComplexShape.up ℤ) z
  let C := CochainComplex.mappingCone (relativeCochainRestrictionInt R X)
  let D := (relativeDualCochainShortComplexInt R X).X₁
  have hn : (1 : ℤ) + ((n : ℤ) - 1) = (n : ℤ) := by lia
  exact
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) ((n : ℤ) - 1)).symm.app C ≪≫
    (H ((n : ℤ) - 1)).mapIso (relativeDualShiftIsoCochainCone R X).symm ≪≫
    (((H 0).shiftIso (1 : ℤ) ((n : ℤ) - 1) (n : ℤ) hn).app (Q.obj D)) ≪≫
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) (n : ℤ)).app D

/-- Relative singular cohomology is the degree-`n - 1` cohomology of the mapping cone of
restriction from ambient singular cochains to subspace singular cochains. -/
def relativeCochainConeCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R]
      RelativeCohomology R X n :=
  (relativeCochainConeHomologyIsoDualRelativeInt R X n).toLinearEquiv |>.trans <|
    (((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv |>.trans <|
      (ShortComplex.homologyMapIso
        (HomologicalComplex.linearDualCochainComplexScIso ((relativeChainFunctor R).obj X) n)
          |>.toLinearEquiv.trans <|
        (((relativeChainFunctor R).obj X).sc n).linearDualHomologyEquiv)

end AlgebraicTopology.Singular
