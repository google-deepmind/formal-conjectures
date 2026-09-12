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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.ChartLocalFundamentalClass
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularExcisionField
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Relative excision for an open neighborhood of a point

This file proves the point-complement form of singular excision needed for local fundamental
classes.  If `U` is an open neighborhood of `x` in a `T₁` space `X`, inclusion induces an
isomorphism

`Hₙ(U, U ∖ {x}; ℚ) ≅ Hₙ(X, X ∖ {x}; ℚ)`.

The proof uses the already established affine-subdivision small-chain theorem for the two-set
cover `U, X ∖ {x}`.  No excision or homology-comparison hypothesis is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Set
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable {X : Type} [TopologicalSpace X] [T1Space X]

/-- The pair `(U, U ∖ {x})` for a subset `U` containing `x`. -/
abbrev neighborhoodPointComplementPair (U : Set X) (x : X) : TopPair :=
  TopPair.ofSubset (X := TopCat.of U) {u | u.1 ≠ x}

/-- The inclusion from a neighborhood point-complement pair into the ambient point-complement
pair. -/
def neighborhoodPointComplementPairMap (U : Set X) (x : X) :
    neighborhoodPointComplementPair U x ⟶ pointComplementPair x :=
  TopPair.ofHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun u ↦ ⟨u.1.1, u.2⟩,
      continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _⟩)
    (by ext u; rfl)

/-- The two-set cover used in point excision: the neighborhood and the complement of the
point. -/
def pointExcisionCover (U : Set X) (x : X) : Bool → Set (TopCat.of X) :=
  fun b ↦ if b then U else {x}ᶜ

lemma pointExcisionCover_isOpen (U : Set X) (x : X) (hU : IsOpen U) :
    ∀ b, IsOpen (pointExcisionCover U x b) := by
  intro b
  cases b with
  | false => exact isClosed_singleton.isOpen_compl
  | true => exact hU

omit [T1Space X] in
lemma pointExcisionCover_iUnion (U : Set X) (x : X) (hx : x ∈ U) :
    ⋃ b, pointExcisionCover U x b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y = x
  · exact Set.mem_iUnion.2 ⟨true, by simpa [pointExcisionCover, hy] using hx⟩
  · exact Set.mem_iUnion.2 ⟨false, by simpa [pointExcisionCover]⟩

/-- Rational chains on the small singular subcomplex for the point-excision cover. -/
abbrev PointExcisionSmallChainComplex (U : Set X) (x : X) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  CoverSmallRationalSingularChainComplex (TopCat.of X) (pointExcisionCover U x)

/-- The inclusion of the point complement into the ambient space, with its codomain fixed
explicitly to avoid transports between definitionally equal presentations of the subspace. -/
def pointComplementAmbientInclusion (x : X) :
    (pointComplementPair x).snd ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun y ↦ y.1, continuous_subtype_val⟩

/-- The identity-on-points map from the point complement to the `false` member of the
point-excision cover. -/
def pointComplementToFalseCoverMember (U : Set X) (x : X) :
    (pointComplementPair x).snd ⟶ TopCat.of (pointExcisionCover U x false) :=
  TopCat.ofHom ⟨Set.codRestrict (pointComplementAmbientInclusion x)
      (pointExcisionCover U x false) (fun y ↦ by change y.1 ≠ x; exact y.2),
    (pointComplementAmbientInclusion x).hom.continuous.codRestrict _⟩

/-- The chain map from the point complement into the small chains. -/
def pointComplementToExcisionSmallSingularSet (U : Set X) (x : X) :
    TopCat.toSSet.obj (pointComplementPair x).snd ⟶
      coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) := by
  refine SSet.Subcomplex.lift
    (TopCat.toSSet.map (pointComplementAmbientInclusion x)) ?_
  intro n z hz
  rw [mem_coverSmallSingularSubcomplex_iff]
  refine ⟨false, ?_⟩
  change z ∈ Set.range ((TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.of X) (pointExcisionCover U x false))).app n)
  obtain ⟨a, rfl⟩ := hz
  refine ⟨(TopCat.toSSet.map (pointComplementToFalseCoverMember U x)).app n a, ?_⟩
  apply ((TopCat.of X).toSSetObjEquiv n).injective
  ext t
  rfl

omit [T1Space X] in
@[reassoc (attr := simp)]
lemma pointComplementToExcisionSmallSingularSet_comp_inclusion
    (U : Set X) (x : X) :
    pointComplementToExcisionSmallSingularSet U x ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x)).ι =
      TopCat.toSSet.map (pointComplementAmbientInclusion x) :=
  SSet.Subcomplex.lift_ι _ _

def pointComplementToExcisionSmallChains (U : Set X) (x : X) :
    (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      PointExcisionSmallChainComplex U x :=
  SSet.chainComplexMap
    (pointComplementToExcisionSmallSingularSet U x)
    (ModuleCat.of ℚ ℚ)

/-- The arrow whose cokernel is the small relative chain complex for point excision. -/
def pointExcisionSmallChainArrow (U : Set X) (x : X) :
    Arrow (ChainCategory ℚ) :=
  Arrow.mk (pointComplementToExcisionSmallChains U x)

/-- The relative quotient of point-excision-small chains by chains avoiding the point. -/
abbrev PointExcisionSmallRelativeChainComplex (U : Set X) (x : X) :
    ChainCategory ℚ :=
  (Limits.coker (C := ChainCategory ℚ)).obj (pointExcisionSmallChainArrow U x)

/-- A small simplex lies away from `x` when it comes from the point-complement member of the
cover. -/
def PointExcisionSmallSimplex.AvoidsPoint (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌) : Prop :=
  ∃ a : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌,
    (TopCat.toSSet.map (pointComplementAmbientInclusion x)).app _ a =
      σ.1

instance (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌) : Decidable (PointExcisionSmallSimplex.AvoidsPoint U x σ) :=
  Classical.propDecidable _

omit [T1Space X] in
lemma PointExcisionSmallSimplex.avoidsPoint_face (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n + 1⦌)
    (hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ) (i : Fin (n + 2)) :
    PointExcisionSmallSimplex.AvoidsPoint U x
      ((coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet).δ i σ) := by
  obtain ⟨a, ha⟩ := hσ
  exact ⟨(TopCat.toSSet.obj (pointComplementPair x).snd).δ i a,
    congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) ha⟩

omit [T1Space X] in
/-- A small simplex which does not avoid `x` comes from the neighborhood member of the cover. -/
lemma PointExcisionSmallSimplex.exists_neighborhoodPreimage (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌)
    (hσ : ¬ PointExcisionSmallSimplex.AvoidsPoint U x σ) :
    ∃ y : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌,
      (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ y = σ.1 := by
  obtain ⟨b, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (TopCat.of X) (pointExcisionCover U x) σ.1).mp σ.2
  cases b with
  | false =>
      dsimp [pointExcisionCover] at y hy
      exact False.elim (hσ ⟨y, hy⟩)
  | true =>
      dsimp [pointExcisionCover] at y hy
      exact ⟨y, hy⟩

/-- The chosen neighborhood lift of a small simplex which does not avoid `x`. -/
def PointExcisionSmallSimplex.neighborhoodPreimage (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌)
    (hσ : ¬ PointExcisionSmallSimplex.AvoidsPoint U x σ) :
    (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌ :=
  Classical.choose (PointExcisionSmallSimplex.exists_neighborhoodPreimage U x σ hσ)

omit [T1Space X] in
lemma PointExcisionSmallSimplex.neighborhoodPreimage_map (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌)
    (hσ : ¬ PointExcisionSmallSimplex.AvoidsPoint U x σ) :
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _
        (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ) = σ.1 :=
  Classical.choose_spec (PointExcisionSmallSimplex.exists_neighborhoodPreimage U x σ hσ)

/-- A singular simplex of `U` which avoids `x` lifts to the subspace `U ∖ {x}`. -/
def neighborhoodPointComplementSimplexOfAvoids (U : Set X) (x : X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (hu : ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ≠ x) :
    (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd) _⦋n⦌ :=
  ((neighborhoodPointComplementPair U x).snd.toSSetObjEquiv _).symm
    ⟨fun t ↦ ⟨((TopCat.of U).toSSetObjEquiv _ u) t, hu t⟩,
      ((TopCat.of U).toSSetObjEquiv _ u).continuous.subtype_mk _⟩

omit [T1Space X] in
lemma neighborhoodPointComplementSimplexOfAvoids_map (U : Set X) (x : X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (hu : ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ≠ x) :
    (TopCat.toSSet.map (neighborhoodPointComplementPair U x).map).app _
        (neighborhoodPointComplementSimplexOfAvoids U x u hu) = u := by
  apply ((TopCat.of U).toSSetObjEquiv _).injective
  ext t
  rfl

omit [T1Space X] in
/-- Equality with a simplex in `X ∖ {x}` shows that a simplex of `U` avoids `x`. -/
lemma neighborhoodSimplex_avoids_of_ambient_eq (U : Set X) (x : X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (a : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌)
    (h : (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ u =
      (TopCat.toSSet.map (pointComplementAmbientInclusion x)).app _ a) :
    ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ≠ x := by
  intro t hut
  have ht := congrArg (fun z ↦ ((TopCat.of X).toSSetObjEquiv _ z) t) h
  change (((TopCat.of U).toSSetObjEquiv _ u) t).1 =
    (((pointComplementPair x).snd.toSSetObjEquiv _ a) t).1 at ht
  exact (((pointComplementPair x).snd.toSSetObjEquiv _ a) t).2
    (by simpa using ht.symm.trans hut)

omit [T1Space X] in
lemma neighborhoodInclusion_singular_injective (U : Set X) {n : ℕ} :
    Function.Injective
      ((TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app
        (Opposite.op (SimplexCategory.mk n))) := by
  intro a b h
  apply ((TopCat.of U).toSSetObjEquiv _).injective
  ext t
  exact congrArg (fun z ↦ ((TopCat.of X).toSSetObjEquiv _ z) t) h

/-- A neighborhood simplex which is also represented in the point complement vanishes after
projection to the neighborhood relative chain complex. -/
abbrev neighborhoodSubspaceChainMap (U : Set X) (x : X) :
    (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (neighborhoodPointComplementPair U x).map)
    (ModuleCat.of ℚ ℚ)

/-- The relative-chain projection for the neighborhood pair, with the absolute neighborhood
chain complex exposed as its source. -/
abbrev neighborhoodRelativeProjection (U : Set X) (x : X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) :=
  relativeChainProjection ℚ (neighborhoodPointComplementPair U x)

def neighborhoodRelativeProjectionComponent (U : Set X) (x : X) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ)).X n ⟶
      (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) |>.X n :=
  (neighborhoodRelativeProjection U x).f n

omit [T1Space X] in
lemma neighborhoodRelativeProjectionComponent_comm (U : Set X) (x : X) (n : ℕ) :
    neighborhoodRelativeProjectionComponent U x (n + 1) ≫
        ((relativeChainFunctor ℚ).obj
          (neighborhoodPointComplementPair U x)).d (n + 1) n =
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex
        (ModuleCat.of ℚ ℚ)).d (n + 1) n ≫
        neighborhoodRelativeProjectionComponent U x n :=
  (relativeChainProjection ℚ (neighborhoodPointComplementPair U x)).comm (n + 1) n

omit [T1Space X] in
lemma neighborhoodSubspaceChainMap_comp_relativeProjection (U : Set X) (x : X) :
    neighborhoodSubspaceChainMap U x ≫
      neighborhoodRelativeProjection U x = 0 :=
  subspaceChainMap_relativeChainProjection ℚ (neighborhoodPointComplementPair U x)

omit [T1Space X] in
lemma neighborhoodSimplex_projection_zero_of_ambient_eq
    (U : Set X) (x : X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (a : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌)
    (h : (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ u =
      (TopCat.toSSet.map (pointComplementAmbientInclusion x)).app _ a) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
        neighborhoodRelativeProjectionComponent U x n = 0 := by
  let hu := neighborhoodSimplex_avoids_of_ambient_eq U x u a h
  let v := neighborhoodPointComplementSimplexOfAvoids U x u hu
  have hv := neighborhoodPointComplementSimplexOfAvoids_map U x u hu
  have hvchain :
      (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).ιChainComplex v ≫
          (neighborhoodSubspaceChainMap U x).f n =
        (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u := by
    change (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).ιChainComplex v ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (neighborhoodPointComplementPair U x).map)
        (ModuleCat.of ℚ ℚ)).f n = _
    rw [SSet.ι_chainComplexMap_f, hv]
    rfl
  have hc := congrArg (fun f ↦ f.f n)
    (neighborhoodSubspaceChainMap_comp_relativeProjection U x)
  change (neighborhoodSubspaceChainMap U x).f n ≫
    neighborhoodRelativeProjectionComponent U x n = 0 at hc
  calc
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
        neighborhoodRelativeProjectionComponent U x n =
      ((TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).ιChainComplex v ≫
        (neighborhoodSubspaceChainMap U x).f n) ≫
          neighborhoodRelativeProjectionComponent U x n := by
            rw [hvchain]
    _ = (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).ιChainComplex v ≫
        ((neighborhoodSubspaceChainMap U x).f n ≫
          neighborhoodRelativeProjectionComponent U x n) := Category.assoc _ _ _
    _ = 0 := by rw [hc, comp_zero]

/-- On a basis simplex, send a point-avoiding simplex to zero and otherwise lift it to the
neighborhood before projecting to relative chains. -/
def pointExcisionSmallToNeighborhoodRelativeComponent (U : Set X) (x : X) (n : ℕ) :
    (PointExcisionSmallChainComplex U x).X n ⟶
      ((relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x)).X n :=
  ((coverSmallSingularSubcomplex (TopCat.of X)
    (pointExcisionCover U x) : SSet).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) n).desc
      (Cofan.mk _ fun σ ↦
        if hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ then 0 else
          (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
              (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ) ≫
            neighborhoodRelativeProjectionComponent U x n)

omit [T1Space X] in
@[reassoc]
lemma iota_pointExcisionSmallToNeighborhoodRelativeComponent
    (U : Set X) (x : X) (n : ℕ)
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌) :
    (coverSmallSingularSubcomplex (TopCat.of X)
      (pointExcisionCover U x) : SSet).ιChainComplex σ ≫
        pointExcisionSmallToNeighborhoodRelativeComponent U x n =
      if hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ then 0 else
        (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
            (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ) ≫
          neighborhoodRelativeProjectionComponent U x n :=
  ((coverSmallSingularSubcomplex (TopCat.of X)
    (pointExcisionCover U x) : SSet).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) n).fac _ (Discrete.mk σ)

omit [T1Space X] in
lemma pointExcisionSmallToNeighborhoodRelativeComponent_comm
    (U : Set X) (x : X) (n : ℕ) :
    pointExcisionSmallToNeighborhoodRelativeComponent U x (n + 1) ≫
        ((relativeChainFunctor ℚ).obj
          (neighborhoodPointComplementPair U x)).d (n + 1) n =
      (PointExcisionSmallChainComplex U x).d (n + 1) n ≫
        pointExcisionSmallToNeighborhoodRelativeComponent U x n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  by_cases hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ
  · rw [← Category.assoc,
      iota_pointExcisionSmallToNeighborhoodRelativeComponent U x (n + 1) σ,
      dif_pos hσ, zero_comp, ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Preadditive.zsmul_comp,
      iota_pointExcisionSmallToNeighborhoodRelativeComponent U x n,
      dif_pos (PointExcisionSmallSimplex.avoidsPoint_face U x σ hσ i)]
    simp
  · rw [← Category.assoc,
      iota_pointExcisionSmallToNeighborhoodRelativeComponent U x (n + 1) σ,
      dif_neg hσ, Category.assoc, neighborhoodRelativeProjectionComponent_comm U x n,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp]
    congr 1
    by_cases hi : PointExcisionSmallSimplex.AvoidsPoint U x
        ((coverSmallSingularSubcomplex (TopCat.of X)
          (pointExcisionCover U x) : SSet).δ i σ)
    · rw [iota_pointExcisionSmallToNeighborhoodRelativeComponent U x n, dif_pos hi]
      obtain ⟨a, ha⟩ := hi
      apply neighborhoodSimplex_projection_zero_of_ambient_eq U x _ a
      have hp := PointExcisionSmallSimplex.neighborhoodPreimage_map U x σ hσ
      exact (congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) hp).trans ha.symm
    · rw [iota_pointExcisionSmallToNeighborhoodRelativeComponent U x n, dif_neg hi]
      congr 1
      apply congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex z)
      apply neighborhoodInclusion_singular_injective U
      have hp := PointExcisionSmallSimplex.neighborhoodPreimage_map U x σ hσ
      exact (congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) hp).trans
        (PointExcisionSmallSimplex.neighborhoodPreimage_map U x _ hi).symm

/-- The chain map from small relative chains to neighborhood relative chains obtained by
discarding simplices which avoid the distinguished point. -/
def pointExcisionSmallToNeighborhoodRelativeChainMap (U : Set X) (x : X) :
    PointExcisionSmallChainComplex U x ⟶
      (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) where
  f n := pointExcisionSmallToNeighborhoodRelativeComponent U x n
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    exact pointExcisionSmallToNeighborhoodRelativeComponent_comm U x j

omit [T1Space X] in
/-- A simplex entering the small complex through the point-complement cover member is recognized
as point-avoiding. -/
lemma pointComplementCoverMember_avoidsPoint (U : Set X) (x : X) {n : ℕ}
    (a : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌) :
    PointExcisionSmallSimplex.AvoidsPoint U x
      ((pointComplementToExcisionSmallSingularSet U x).app _ a) := by
  refine ⟨a, ?_⟩
  have h := congr_app
    (pointComplementToExcisionSmallSingularSet_comp_inclusion U x)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h a).symm

omit [T1Space X] in
/-- The small-to-neighborhood chain map kills all chains from the point complement. -/
lemma pointComplementToExcisionSmallChains_comp_smallToNeighborhood
    (U : Set X) (x : X) :
    pointComplementToExcisionSmallChains U x ≫
      pointExcisionSmallToNeighborhoodRelativeChainMap U x = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap (pointComplementToExcisionSmallSingularSet U x)
      (ModuleCat.of ℚ ℚ)).f n ≫
        pointExcisionSmallToNeighborhoodRelativeComponent U x n = 0
  apply SSet.chainComplex_hom_ext
  intro a
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_pointExcisionSmallToNeighborhoodRelativeComponent,
    dif_pos (pointComplementCoverMember_avoidsPoint U x a)]
  rfl

/-- Projection from small chains to the small relative quotient. -/
abbrev pointExcisionSmallRelativeProjection (U : Set X) (x : X) :
    PointExcisionSmallChainComplex U x ⟶
      PointExcisionSmallRelativeChainComplex U x :=
  cokernel.π (pointComplementToExcisionSmallChains U x)

/-- The chain map from the small relative quotient back to neighborhood relative chains. -/
def pointExcisionSmallRelativeToNeighborhoodRelativeChainMap (U : Set X) (x : X) :
    PointExcisionSmallRelativeChainComplex U x ⟶
      (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) :=
  cokernel.desc (pointComplementToExcisionSmallChains U x)
    (pointExcisionSmallToNeighborhoodRelativeChainMap U x)
    (pointComplementToExcisionSmallChains_comp_smallToNeighborhood U x)

omit [T1Space X] in
@[reassoc (attr := simp)]
lemma pointExcisionSmallRelativeProjection_comp_toNeighborhood
    (U : Set X) (x : X) :
    pointExcisionSmallRelativeProjection U x ≫
        pointExcisionSmallRelativeToNeighborhoodRelativeChainMap U x =
      pointExcisionSmallToNeighborhoodRelativeChainMap U x :=
  cokernel.π_desc _ _ _

/-- The inclusion from `U ∖ {x}` to `X ∖ {x}`. -/
def neighborhoodPointComplementToPointComplement (U : Set X) (x : X) :
    (neighborhoodPointComplementPair U x).snd ⟶ (pointComplementPair x).snd :=
  TopCat.ofHom ⟨fun u ↦ ⟨u.1.1, u.2⟩,
    continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _⟩

/-- The identity-on-points map from the neighborhood to the `true` member of the
point-excision cover. -/
def neighborhoodToTrueCoverMember (U : Set X) (x : X) :
    TopCat.of U ⟶ TopCat.of (pointExcisionCover U x true) :=
  TopCat.ofHom ⟨Set.codRestrict (topologicalSubsetInclusion (TopCat.of X) U)
      (pointExcisionCover U x true) (fun y ↦ by change y.1 ∈ U; exact y.2),
    (topologicalSubsetInclusion (TopCat.of X) U).hom.continuous.codRestrict _⟩

/-- The chain map from neighborhood chains to the point-excision-small chains. -/
def neighborhoodToPointExcisionSmallSingularSet (U : Set X) (x : X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶
      coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) := by
  refine SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)) ?_
  intro n z hz
  rw [mem_coverSmallSingularSubcomplex_iff]
  refine ⟨true, ?_⟩
  change z ∈ Set.range ((TopCat.toSSet.map
    (topologicalSubsetInclusion (TopCat.of X) (pointExcisionCover U x true))).app n)
  obtain ⟨a, rfl⟩ := hz
  refine ⟨(TopCat.toSSet.map (neighborhoodToTrueCoverMember U x)).app n a, ?_⟩
  apply ((TopCat.of X).toSSetObjEquiv n).injective
  ext t
  rfl

omit [T1Space X] in
@[reassoc (attr := simp)]
lemma neighborhoodToPointExcisionSmallSingularSet_comp_inclusion
    (U : Set X) (x : X) :
    neighborhoodToPointExcisionSmallSingularSet U x ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x)).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U) :=
  SSet.Subcomplex.lift_ι _ _

def neighborhoodToPointExcisionSmallChains (U : Set X) (x : X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      PointExcisionSmallChainComplex U x :=
  SSet.chainComplexMap
    (neighborhoodToPointExcisionSmallSingularSet U x)
    (ModuleCat.of ℚ ℚ)

/-- The chain map from `U ∖ {x}` to `X ∖ {x}`. -/
def neighborhoodPointComplementToPointComplementChains (U : Set X) (x : X) :
    (TopCat.toSSet.obj (neighborhoodPointComplementPair U x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map (neighborhoodPointComplementToPointComplement U x))
    (ModuleCat.of ℚ ℚ)

omit [T1Space X] in
lemma neighborhoodPointComplementToSmall_sSet_square (U : Set X) (x : X) :
    TopCat.toSSet.map (neighborhoodPointComplementToPointComplement U x) ≫
        pointComplementToExcisionSmallSingularSet U x =
      TopCat.toSSet.map (neighborhoodPointComplementPair U x).map ≫
        neighborhoodToPointExcisionSmallSingularSet U x := by
  ext n y
  apply Subtype.ext
  apply ((TopCat.of X).toSSetObjEquiv n).injective
  ext t
  rfl

omit [T1Space X] in
lemma neighborhoodPointComplementToSmall_chain_square (U : Set X) (x : X) :
    neighborhoodPointComplementToPointComplementChains U x ≫
        pointComplementToExcisionSmallChains U x =
      neighborhoodSubspaceChainMap U x ≫
        neighborhoodToPointExcisionSmallChains U x := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  have h := F.congr_map (neighborhoodPointComplementToSmall_sSet_square U x)
  calc
    neighborhoodPointComplementToPointComplementChains U x ≫
        pointComplementToExcisionSmallChains U x =
      F.map (TopCat.toSSet.map (neighborhoodPointComplementToPointComplement U x) ≫
        pointComplementToExcisionSmallSingularSet U x) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (neighborhoodPointComplementPair U x).map ≫
        neighborhoodToPointExcisionSmallSingularSet U x) := h
    _ = neighborhoodSubspaceChainMap U x ≫
        neighborhoodToPointExcisionSmallChains U x := F.map_comp _ _

/-- The morphism of chain-complex arrows from the neighborhood pair to the small pair. -/
def neighborhoodPairChainsToPointExcisionSmallArrow (U : Set X) (x : X) :
    (chainPairFunctor ℚ).obj (neighborhoodPointComplementPair U x) ⟶
      pointExcisionSmallChainArrow U x :=
  Arrow.homMk
    (neighborhoodPointComplementToPointComplementChains U x)
    (neighborhoodToPointExcisionSmallChains U x)
    (neighborhoodPointComplementToSmall_chain_square U x)

/-- Inclusion of the neighborhood pair into the small relative quotient. -/
def neighborhoodRelativeToPointExcisionSmallRelativeChainMap (U : Set X) (x : X) :
    (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) ⟶
      PointExcisionSmallRelativeChainComplex U x :=
  (Limits.coker (C := ChainCategory ℚ)).map
    (neighborhoodPairChainsToPointExcisionSmallArrow U x)

omit [T1Space X] in
@[reassoc]
lemma neighborhoodRelativeProjection_comp_toPointExcisionSmall
    (U : Set X) (x : X) :
    neighborhoodRelativeProjection U x ≫
        neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x =
      neighborhoodToPointExcisionSmallChains U x ≫
        pointExcisionSmallRelativeProjection U x :=
  ((coker.π (C := ChainCategory ℚ)).naturality
    (neighborhoodPairChainsToPointExcisionSmallArrow U x)).symm

omit [T1Space X] in
lemma pointComplementCoverMember_eq_of_avoidsPoint
    (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌)
    (a : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌)
    (ha : (TopCat.toSSet.map (pointComplementAmbientInclusion x)).app _ a = σ.1) :
    (pointComplementToExcisionSmallSingularSet U x).app _ a = σ := by
  apply Subtype.ext
  have h := congr_app
    (pointComplementToExcisionSmallSingularSet_comp_inclusion U x)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h a).trans ha

omit [T1Space X] in
lemma neighborhoodCoverMember_eq_of_not_avoidsPoint
    (U : Set X) (x : X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x) : SSet)
      _⦋n⦌)
    (hσ : ¬ PointExcisionSmallSimplex.AvoidsPoint U x σ) :
    (neighborhoodToPointExcisionSmallSingularSet U x).app _
        (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ) = σ := by
  apply Subtype.ext
  have h := congr_app
    (neighborhoodToPointExcisionSmallSingularSet_comp_inclusion U x)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h
    (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ)).trans
      (PointExcisionSmallSimplex.neighborhoodPreimage_map U x σ hσ)

omit [T1Space X] in
/-- Going from small chains to neighborhood relative chains and back to the small relative
quotient is the canonical small-relative projection. -/
lemma pointExcisionSmallToNeighborhood_comp_toSmallRelative
    (U : Set X) (x : X) :
    pointExcisionSmallToNeighborhoodRelativeChainMap U x ≫
        neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x =
      pointExcisionSmallRelativeProjection U x := by
  apply HomologicalComplex.hom_ext
  intro n
  change pointExcisionSmallToNeighborhoodRelativeComponent U x n ≫
      (neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x).f n =
    (pointExcisionSmallRelativeProjection U x).f n
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, iota_pointExcisionSmallToNeighborhoodRelativeComponent]
  by_cases hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ
  · rw [dif_pos hσ, zero_comp]
    symm
    obtain ⟨a, ha⟩ := hσ
    rw [← pointComplementCoverMember_eq_of_avoidsPoint U x σ a ha,
      ← SSet.ι_chainComplexMap_f, Category.assoc]
    have hc := congrArg (fun f ↦ f.f n)
      (cokernel.condition (pointComplementToExcisionSmallChains U x))
    change (pointComplementToExcisionSmallChains U x).f n ≫
      (pointExcisionSmallRelativeProjection U x).f n = 0 at hc
    change (TopCat.toSSet.obj (pointComplementPair x).snd).ιChainComplex a ≫
      ((pointComplementToExcisionSmallChains U x).f n ≫
        (pointExcisionSmallRelativeProjection U x).f n) = 0
    rw [hc, comp_zero]
  · rw [dif_neg hσ, Category.assoc]
    have hc := congrArg (fun f ↦ f.f n)
      (neighborhoodRelativeProjection_comp_toPointExcisionSmall U x)
    change neighborhoodRelativeProjectionComponent U x n ≫
        (neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x).f n =
      (neighborhoodToPointExcisionSmallChains U x).f n ≫
        (pointExcisionSmallRelativeProjection U x).f n at hc
    rw [hc, ← Category.assoc]
    change ((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
        (PointExcisionSmallSimplex.neighborhoodPreimage U x σ hσ) ≫
      (SSet.chainComplexMap (neighborhoodToPointExcisionSmallSingularSet U x)
        (ModuleCat.of ℚ ℚ)).f n) ≫
      (pointExcisionSmallRelativeProjection U x).f n = _
    rw [SSet.ι_chainComplexMap_f,
      neighborhoodCoverMember_eq_of_not_avoidsPoint U x σ hσ]

omit [T1Space X] in
/-- Restricting neighborhood chains to the small complex and then applying the explicit
small-to-relative map is the ordinary neighborhood-relative projection. -/
lemma neighborhoodToPointExcisionSmall_comp_smallToNeighborhood
    (U : Set X) (x : X) :
    neighborhoodToPointExcisionSmallChains U x ≫
        pointExcisionSmallToNeighborhoodRelativeChainMap U x =
      neighborhoodRelativeProjection U x := by
  apply HomologicalComplex.hom_ext
  intro n
  change (neighborhoodToPointExcisionSmallChains U x).f n ≫
      pointExcisionSmallToNeighborhoodRelativeComponent U x n =
    neighborhoodRelativeProjectionComponent U x n
  apply SSet.chainComplex_hom_ext
  intro u
  rw [← Category.assoc]
  change ((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
      (SSet.chainComplexMap (neighborhoodToPointExcisionSmallSingularSet U x)
        (ModuleCat.of ℚ ℚ)).f n) ≫
      pointExcisionSmallToNeighborhoodRelativeComponent U x n = _
  rw [SSet.ι_chainComplexMap_f]
  let σ := (neighborhoodToPointExcisionSmallSingularSet U x).app _ u
  change (coverSmallSingularSubcomplex (TopCat.of X)
      (pointExcisionCover U x) : SSet).ιChainComplex σ ≫
      pointExcisionSmallToNeighborhoodRelativeComponent U x n = _
  rw [iota_pointExcisionSmallToNeighborhoodRelativeComponent]
  have hs := congr_app
    (neighborhoodToPointExcisionSmallSingularSet_comp_inclusion U x)
    (Opposite.op (SimplexCategory.mk n))
  have hsu := ConcreteCategory.congr_hom hs u
  change σ.1 =
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ u at hsu
  by_cases hσ : PointExcisionSmallSimplex.AvoidsPoint U x σ
  · rw [dif_pos hσ]
    symm
    obtain ⟨a, ha⟩ := hσ
    exact neighborhoodSimplex_projection_zero_of_ambient_eq U x u a (hsu.symm.trans ha.symm)
  · rw [dif_neg hσ]
    congr 1
    apply congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex z)
    apply neighborhoodInclusion_singular_injective U
    exact (PointExcisionSmallSimplex.neighborhoodPreimage_map U x σ hσ).trans hsu

omit [T1Space X] in
/-- The two explicit maps between neighborhood-relative and small-relative chains are inverse
in the small-to-neighborhood order. -/
lemma pointExcisionSmallRelativeToNeighborhood_comp_neighborhoodToSmall
    (U : Set X) (x : X) :
    pointExcisionSmallRelativeToNeighborhoodRelativeChainMap U x ≫
        neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x =
      𝟙 (PointExcisionSmallRelativeChainComplex U x) := by
  let : Epi (pointExcisionSmallRelativeProjection U x) := by
    change Epi (colimit.ι
      (parallelPair (pointComplementToExcisionSmallChains U x) 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi (pointExcisionSmallRelativeProjection U x)).1
  rw [← Category.assoc, pointExcisionSmallRelativeProjection_comp_toNeighborhood,
    pointExcisionSmallToNeighborhood_comp_toSmallRelative, Category.comp_id]

omit [T1Space X] in
lemma neighborhoodToSmallProjection_comp_toNeighborhood
    (U : Set X) (x : X) :
    (neighborhoodToPointExcisionSmallChains U x ≫
      pointExcisionSmallRelativeProjection U x) ≫
        pointExcisionSmallRelativeToNeighborhoodRelativeChainMap U x =
        neighborhoodRelativeProjection U x := by
  rw [Category.assoc, pointExcisionSmallRelativeProjection_comp_toNeighborhood]
  exact neighborhoodToPointExcisionSmall_comp_smallToNeighborhood U x

omit [T1Space X] in
/-- The two explicit maps between neighborhood-relative and small-relative chains are inverse
in the neighborhood-to-small order. -/
lemma neighborhoodToSmall_comp_pointExcisionSmallRelativeToNeighborhood
    (U : Set X) (x : X) :
    neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x ≫
        pointExcisionSmallRelativeToNeighborhoodRelativeChainMap U x =
      𝟙 ((relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x)) := by
  let : Epi (neighborhoodRelativeProjection U x) := by
    change Epi (colimit.ι
      (parallelPair
        ((chainPairFunctor ℚ).obj (neighborhoodPointComplementPair U x)).hom 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi
    (neighborhoodRelativeProjection U x)).1
  rw [neighborhoodRelativeProjection_comp_toPointExcisionSmall_assoc,
    ← Category.assoc, neighborhoodToSmallProjection_comp_toNeighborhood, Category.comp_id]

/-- Neighborhood-relative chains are isomorphic to the point-excision-small relative
quotient. -/
def neighborhoodRelativePointExcisionSmallIso (U : Set X) (x : X) :
    (relativeChainFunctor ℚ).obj (neighborhoodPointComplementPair U x) ≅
      PointExcisionSmallRelativeChainComplex U x where
  hom := neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x
  inv := pointExcisionSmallRelativeToNeighborhoodRelativeChainMap U x
  hom_inv_id := neighborhoodToSmall_comp_pointExcisionSmallRelativeToNeighborhood U x
  inv_hom_id := pointExcisionSmallRelativeToNeighborhood_comp_neighborhoodToSmall U x

omit [T1Space X] in
lemma pointComplementAmbientInclusion_eq_pairMap (x : X) :
    pointComplementAmbientInclusion x = (pointComplementPair x).map := by
  ext y
  rfl

/-- The chain inclusion for the ambient point-complement pair, with both singular chain
complexes exposed. -/
abbrev ambientPointComplementSubspaceChainMap (x : X) :
    (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  ((chainPairFunctor ℚ).obj (pointComplementPair x)).hom

/-- The explicit singular-chain map underlying the ambient point-complement inclusion. -/
def pointComplementAmbientChainMap (x : X) :
    (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (pointComplementAmbientInclusion x))
    (ModuleCat.of ℚ ℚ)

omit [T1Space X] in
lemma pointComplementAmbientChainMap_eq_subspaceChainMap (x : X) :
    pointComplementAmbientChainMap x = ambientPointComplementSubspaceChainMap x := by
  rw [pointComplementAmbientChainMap, pointComplementAmbientInclusion_eq_pairMap]
  rfl

instance pointComplementAmbientInclusion_mono (x : X) :
    Mono (pointComplementAmbientInclusion x) :=
  (TopCat.mono_iff_injective _).2 fun _ _ h ↦ Subtype.ext h

instance pointComplementAmbientChainMap_mono (x : X) :
    Mono (pointComplementAmbientChainMap x) := by
  dsimp [pointComplementAmbientChainMap, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

instance ambientPointComplementSubspaceChainMap_mono (x : X) :
    Mono (ambientPointComplementSubspaceChainMap x) := by
  rw [← pointComplementAmbientChainMap_eq_subspaceChainMap]
  infer_instance

/-- The ambient relative-chain projection, with its absolute chain source exposed. -/
abbrev ambientPointComplementRelativeProjection (x : X) :
    (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (relativeChainFunctor ℚ).obj (pointComplementPair x) :=
  relativeChainProjection ℚ (pointComplementPair x)

omit [T1Space X] in
/-- The point-complement-to-small map followed by small-chain inclusion is the ordinary
point-complement chain inclusion. -/
lemma pointComplementToExcisionSmallChains_comp_ambientInclusion
    (U : Set X) (x : X) :
    pointComplementToExcisionSmallChains U x ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) =
      ambientPointComplementSubspaceChainMap x := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc
    pointComplementToExcisionSmallChains U x ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) =
      F.map (pointComplementToExcisionSmallSingularSet U x ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x)).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (pointComplementAmbientInclusion x)) := by
      rw [pointComplementToExcisionSmallSingularSet_comp_inclusion]
    _ = ambientPointComplementSubspaceChainMap x := by
      rw [pointComplementAmbientInclusion_eq_pairMap]
      rfl

instance pointComplementToExcisionSmallChains_mono (U : Set X) (x : X) :
    Mono (pointComplementToExcisionSmallChains U x) :=
  mono_of_mono_fac
    (pointComplementToExcisionSmallChains_comp_ambientInclusion U x)

/-- The identity map on point-complement chains, with the codomain presented as the left
object of the ambient chain-pair arrow. -/
def pointComplementChainsToAmbientPairLeft (x : X) :
    (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      ((chainPairFunctor ℚ).obj (pointComplementPair x)).left :=
  𝟙 _

/-- The inverse identity map for `pointComplementChainsToAmbientPairLeft`. -/
def ambientPairLeftToPointComplementChains (x : X) :
    ((chainPairFunctor ℚ).obj (pointComplementPair x)).left ⟶
      (TopCat.toSSet.obj (pointComplementPair x).snd).chainComplex
        (ModuleCat.of ℚ ℚ) :=
  𝟙 _

instance pointComplementChainsToAmbientPairLeft_isIso (x : X) :
    IsIso (pointComplementChainsToAmbientPairLeft x) := by
  exact ⟨⟨ambientPairLeftToPointComplementChains x, Category.comp_id _, Category.comp_id _⟩⟩

omit [T1Space X] in
lemma pointComplementChainsToAmbientPairLeft_comp
    (U : Set X) (x : X) :
    pointComplementChainsToAmbientPairLeft x ≫
        ((chainPairFunctor ℚ).obj (pointComplementPair x)).hom =
      pointComplementToExcisionSmallChains U x ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) := by
  change 𝟙 _ ≫ ambientPointComplementSubspaceChainMap x = _
  rw [Category.id_comp]
  exact (pointComplementToExcisionSmallChains_comp_ambientInclusion U x).symm

/-- The morphism of chain-pair arrows from the point-excision-small pair to the ambient
point-complement pair. -/
def pointExcisionSmallToAmbientPairArrow (U : Set X) (x : X) :
    pointExcisionSmallChainArrow U x ⟶
      (chainPairFunctor ℚ).obj (pointComplementPair x) :=
  Arrow.homMk
    (pointComplementChainsToAmbientPairLeft x)
    (coverSmallRationalSingularChainInclusion
      (TopCat.of X) (pointExcisionCover U x))
    (pointComplementChainsToAmbientPairLeft_comp U x)

/-- The map from the point-excision-small relative quotient to ambient relative chains. -/
def pointExcisionSmallRelativeToAmbientRelativeChainMap (U : Set X) (x : X) :
    PointExcisionSmallRelativeChainComplex U x ⟶
      (relativeChainFunctor ℚ).obj (pointComplementPair x) :=
  (Limits.coker (C := ChainCategory ℚ)).map
    (pointExcisionSmallToAmbientPairArrow U x)

omit [T1Space X] in
@[reassoc]
lemma pointExcisionSmallRelativeProjection_comp_toAmbient
    (U : Set X) (x : X) :
    pointExcisionSmallRelativeProjection U x ≫
        pointExcisionSmallRelativeToAmbientRelativeChainMap U x =
      coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) ≫
        ambientPointComplementRelativeProjection x :=
  ((coker.π (C := ChainCategory ℚ)).naturality
    (pointExcisionSmallToAmbientPairArrow U x)).symm

/-- The morphism between the two cokernel short complexes used in point excision. -/
def pointExcisionSmallToAmbientCokernelSequenceHom (U : Set X) (x : X) :
    ShortComplex.cokernelSequence (pointComplementToExcisionSmallChains U x) ⟶
      ShortComplex.cokernelSequence
        (ambientPointComplementSubspaceChainMap x) :=
  ShortComplex.homMk
    (pointComplementChainsToAmbientPairLeft x)
    (coverSmallRationalSingularChainInclusion
      (TopCat.of X) (pointExcisionCover U x))
    (pointExcisionSmallRelativeToAmbientRelativeChainMap U x)
    (pointComplementChainsToAmbientPairLeft_comp U x)
    (pointExcisionSmallRelativeProjection_comp_toAmbient U x).symm

omit [T1Space X] in
lemma pointExcisionSmallCokernelSequence_shortExact (U : Set X) (x : X) :
    (ShortComplex.cokernelSequence
      (pointComplementToExcisionSmallChains U x)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (pointComplementToExcisionSmallChains U x)
    infer_instance
  epi_g := by infer_instance

omit [T1Space X] in
lemma ambientPointComplementCokernelSequence_shortExact (x : X) :
    (ShortComplex.cokernelSequence
      (ambientPointComplementSubspaceChainMap x)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (ambientPointComplementSubspaceChainMap x)
    infer_instance
  epi_g := by infer_instance

omit [T1Space X] in
lemma pointComplementChainsToAmbientPairLeft_quasiIso (x : X) :
    QuasiIso (pointComplementChainsToAmbientPairLeft x) :=
  inferInstance

/-- The small relative quotient is quasi-isomorphic to ambient relative chains when the
two-set point-excision cover is open and covers the ambient space. -/
theorem pointExcisionSmallRelativeToAmbient_quasiIso
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    QuasiIso (pointExcisionSmallRelativeToAmbientRelativeChainMap U x) := by
  let e := coverSmallRationalChainHomotopyEquiv_of_openCover
    (TopCat.of X) (pointExcisionCover U x)
      (pointExcisionCover_isOpen U x hU) (pointExcisionCover_iUnion U x hx)
  have hsmall : QuasiIso e.hom := e.quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hsmall
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (pointExcisionSmallToAmbientCokernelSequenceHom U x)
    (pointExcisionSmallCokernelSequence_shortExact U x)
    (ambientPointComplementCokernelSequence_shortExact x)
    (pointComplementChainsToAmbientPairLeft_quasiIso x)
    hsmall

/-- The ordinary chain map induced by inclusion of the neighborhood into the ambient space. -/
def neighborhoodAmbientChainMap (U : Set X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U))
    (ModuleCat.of ℚ ℚ)

omit [T1Space X] in
lemma neighborhoodToPointExcisionSmallChains_comp_ambientInclusion
    (U : Set X) (x : X) :
    neighborhoodToPointExcisionSmallChains U x ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) =
      neighborhoodAmbientChainMap U := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc
    neighborhoodToPointExcisionSmallChains U x ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (pointExcisionCover U x) =
      F.map (neighborhoodToPointExcisionSmallSingularSet U x ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (pointExcisionCover U x)).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of X) U)) := by
      rw [neighborhoodToPointExcisionSmallSingularSet_comp_inclusion]
    _ = neighborhoodAmbientChainMap U := rfl

omit [T1Space X] in
lemma neighborhoodAmbientChainMap_eq_pairMapRight (U : Set X) (x : X) :
    neighborhoodAmbientChainMap U =
      ((chainPairFunctor ℚ).map (neighborhoodPointComplementPairMap U x)).right := by
  rfl

omit [T1Space X] in
@[reassoc]
lemma neighborhoodRelativeProjection_comp_ambientRelativeMap
    (U : Set X) (x : X) :
    neighborhoodRelativeProjection U x ≫
        (relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x) =
      neighborhoodAmbientChainMap U ≫
        ambientPointComplementRelativeProjection x := by
  rw [neighborhoodAmbientChainMap_eq_pairMapRight]
  exact ((coker.π (C := ChainCategory ℚ)).naturality
    ((chainPairFunctor ℚ).map (neighborhoodPointComplementPairMap U x))).symm

omit [T1Space X] in
lemma neighborhoodToSmallProjection_comp_toAmbient
    (U : Set X) (x : X) :
    (neighborhoodToPointExcisionSmallChains U x ≫
        pointExcisionSmallRelativeProjection U x) ≫
      pointExcisionSmallRelativeToAmbientRelativeChainMap U x =
        neighborhoodAmbientChainMap U ≫
          ambientPointComplementRelativeProjection x := by
  rw [Category.assoc, pointExcisionSmallRelativeProjection_comp_toAmbient,
    ← Category.assoc, neighborhoodToPointExcisionSmallChains_comp_ambientInclusion]

omit [T1Space X] in
/-- Factoring the neighborhood pair through point-excision-small relative chains gives the
canonical map of relative chain complexes. -/
lemma neighborhoodToSmallRelative_comp_smallRelativeToAmbient
    (U : Set X) (x : X) :
    neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x ≫
        pointExcisionSmallRelativeToAmbientRelativeChainMap U x =
      (relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x) := by
  let : Epi (neighborhoodRelativeProjection U x) := by
    change Epi (colimit.ι
      (parallelPair
        ((chainPairFunctor ℚ).obj (neighborhoodPointComplementPair U x)).hom 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi (neighborhoodRelativeProjection U x)).1
  rw [neighborhoodRelativeProjection_comp_toPointExcisionSmall_assoc,
    ← Category.assoc, neighborhoodToSmallProjection_comp_toAmbient,
    neighborhoodRelativeProjection_comp_ambientRelativeMap]

/-- Inclusion of an open neighborhood induces a quasi-isomorphism on the relative chain
complexes defined by removing the distinguished point. -/
theorem neighborhoodPointComplement_relativeChainMap_quasiIso
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    QuasiIso
      ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) := by
  let : IsIso (neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x) :=
    (neighborhoodRelativePointExcisionSmallIso U x).isIso_hom
  let : QuasiIso (neighborhoodRelativeToPointExcisionSmallRelativeChainMap U x) :=
    inferInstance
  let : QuasiIso (pointExcisionSmallRelativeToAmbientRelativeChainMap U x) :=
    pointExcisionSmallRelativeToAmbient_quasiIso U x hU hx
  rw [← neighborhoodToSmallRelative_comp_smallRelativeToAmbient]
  infer_instance

/-- The canonical isomorphism on relative homology induced by inclusion of an open
neighborhood of the distinguished point. -/
def neighborhoodPointComplementRelativeHomologyIso
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    RelativeHomology ℚ (neighborhoodPointComplementPair U x) n ≅
      RelativeHomology ℚ (pointComplementPair x) n := by
  let : QuasiIso
      ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) :=
    neighborhoodPointComplement_relativeChainMap_quasiIso U x hU hx
  exact isoOfQuasiIsoAt
    ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) n

/-- The map on relative homology induced by an open neighborhood inclusion is bijective. -/
theorem neighborhoodPointComplement_relativeHomologyMap_bijective
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    Function.Bijective
      (relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap U x)) := by
  let : QuasiIso
      ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) :=
    neighborhoodPointComplement_relativeChainMap_quasiIso U x hU hx
  have hIso : IsIso ((relativeHomologyFunctor ℚ n).map
      (neighborhoodPointComplementPairMap U x)) := by
    change IsIso (HomologicalComplex.homologyMap
      ((relativeChainFunctor ℚ).map (neighborhoodPointComplementPairMap U x)) n)
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hIso

/-- In particular, inclusion of an open neighborhood is surjective on relative homology. -/
theorem neighborhoodPointComplement_relativeHomologyMap_surjective
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) (n : ℕ) :
    Function.Surjective
      (relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap U x)) :=
  (neighborhoodPointComplement_relativeHomologyMap_bijective U x hU hx n).2

end AlgebraicTopology.Singular
