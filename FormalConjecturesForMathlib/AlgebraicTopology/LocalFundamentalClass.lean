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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology

/-!
# A standard local fundamental cycle

This file constructs a canonical relative singular cycle in
`H_d(ℝ^d, ℝ^d ∖ {0}; ℚ)`. The affine simplex has vertices the standard basis and
`(-1, ..., -1)`. Its barycenter is the unique point that maps to the origin, while each face
misses the origin. Its relative boundary therefore vanishes.

This explicit cycle fixes the ordering and sign convention needed to normalize local Thom and
fundamental classes without adding an orientation as arbitrary data.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The ordered real coordinate space used for the standard local class. -/
abbrev StandardRealModel (d : ℕ) := Fin d → ℝ

/-- The pair consisting of real coordinate space and the complement of its origin. -/
abbrev standardPuncturedPair (d : ℕ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (StandardRealModel d))
    ({0}ᶜ : Set (StandardRealModel d))

/-- The affine `d`-simplex with vertices the standard basis and the vector `(-1, ..., -1)`. -/
def standardAffineSimplex (d : ℕ) (t : stdSimplex ℝ (Fin (d + 1))) :
    StandardRealModel d :=
  fun j => t (Fin.castSucc j) - t (Fin.last d)

-- Mathlib proves this but does not tag it, so `fun_prop` cannot see through `stdSimplex.map`.
attribute [fun_prop] stdSimplex.continuous_map

@[fun_prop]
lemma continuous_standardAffineSimplex (d : ℕ) : Continuous (standardAffineSimplex d) :=
  continuous_pi fun j =>
    ((continuous_apply (Fin.castSucc j)).comp continuous_subtype_val).sub
      ((continuous_apply (Fin.last d)).comp continuous_subtype_val)

lemma stdSimplex_map_succAbove_self_zero (n : ℕ) (i : Fin (n + 2))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    stdSimplex.map i.succAbove t i = 0 := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove) t i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  simp

lemma standardAffineSimplex_ne_zero_of_coord_zero (d : ℕ)
    (t : stdSimplex ℝ (Fin (d + 1))) (i : Fin (d + 1)) (hi : t i = 0) :
    standardAffineSimplex d t ≠ 0 := by
  intro h
  have hcoord (j : Fin d) : t (Fin.castSucc j) = t (Fin.last d) := by
    have hj := congr_fun h j
    simpa [standardAffineSimplex] using sub_eq_zero.mp hj
  have hlast : t (Fin.last d) = 0 := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact (hcoord j).symm.trans hi
    · exact hi
  have hall (j : Fin (d + 1)) : t j = 0 := by
    rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
    · exact (hcoord k).trans hlast
    · exact hlast
  have hsum := t.2.2
  have hzero : ∑ j, (t : Fin (d + 1) → ℝ) j = 0 :=
    Finset.sum_eq_zero fun j _ => hall j
  exact zero_ne_one (hzero.symm.trans hsum)

lemma standardAffineSimplex_eq_zero_iff (d : ℕ)
    (t : stdSimplex ℝ (Fin (d + 1))) :
    standardAffineSimplex d t = 0 ↔ t = stdSimplex.barycenter := by
  constructor
  · intro h
    have hcoord (j : Fin d) : t (Fin.castSucc j) = t (Fin.last d) := by
      have hj := congr_fun h j
      simpa [standardAffineSimplex] using sub_eq_zero.mp hj
    have hall (j : Fin (d + 1)) : t j = t (Fin.last d) := by
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · exact hcoord k
      · rfl
    have hsum : ∑ _ : Fin (d + 1), t (Fin.last d) = 1 := by
      rw [← t.2.2]
      exact Finset.sum_congr rfl fun j _ => (hall j).symm
    have hcard : (Fintype.card (Fin (d + 1)) : ℝ) ≠ 0 := by
      simp only [Fintype.card_fin]
      positivity
    have hlast : t (Fin.last d) = (Fintype.card (Fin (d + 1)) : ℝ)⁻¹ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      exact ((mul_eq_one_iff_inv_eq₀ hcard).mp hsum).symm
    apply stdSimplex.ext
    funext j
    rw [hall j, hlast]
    exact stdSimplex.barycenter_apply j |>.symm
  · rintro rfl
    ext j
    change (stdSimplex.barycenter : stdSimplex ℝ (Fin (d + 1)))
      (Fin.castSucc j) - stdSimplex.barycenter (Fin.last d) = 0
    exact sub_self _

/-- The continuous affine simplex underlying the standard local cycle. -/
def standardAffineSimplexMap (d : ℕ) :
    C(stdSimplex ℝ (Fin (d + 1)), StandardRealModel d) where
  toFun := standardAffineSimplex d
  continuous_toFun := continuous_standardAffineSimplex d

/-- The affine simplex as a singular simplex of real coordinate space. -/
def standardSingularSimplex (d : ℕ) :
    (TopCat.toSSet.obj (standardPuncturedPair d).fst) _⦋d⦌ :=
  ((standardPuncturedPair d).fst.toSSetObjEquiv _).symm
    (standardAffineSimplexMap d)

/-- A face of the positive-dimensional standard simplex, lifted to the punctured space. -/
def standardFaceMap (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)),
      ({0}ᶜ : Set (StandardRealModel (n + 1)))) where
  toFun t := ⟨standardAffineSimplex (n + 1) (stdSimplex.map i.succAbove t),
    standardAffineSimplex_ne_zero_of_coord_zero (n + 1) _ i
      (stdSimplex_map_succAbove_self_zero n i t)⟩
  continuous_toFun := by fun_prop

/-- A face of the positive-dimensional standard simplex as a singular simplex of the
punctured space. -/
def standardFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).snd) _⦋n⦌ :=
  ((standardPuncturedPair (n + 1)).snd.toSSetObjEquiv _).symm
    (standardFaceMap n i)

lemma standardFaceSimplex_map (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.map (standardPuncturedPair (n + 1)).map).app _
      (standardFaceSimplex n i) =
    (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).δ i
      (standardSingularSimplex (n + 1)) := by
  apply ((standardPuncturedPair (n + 1)).fst.toSSetObjEquiv _).injective
  ext t
  rfl

/-- The relative singular chain complex of the standard punctured real coordinate space. -/
abbrev standardLocalRelativeChainComplex (d : ℕ) :=
  (relativeChainFunctor ℚ).obj (standardPuncturedPair d)

/-- A component of the projection to the standard relative chain complex. -/
def standardLocalProjectionComponent (d k : ℕ) :
    ((chainPairFunctor ℚ).obj (standardPuncturedPair d)).right.X k ⟶
      (standardLocalRelativeChainComplex d).X k :=
  (relativeChainProjection ℚ (standardPuncturedPair d)).f k

/-- The standard affine simplex as an absolute singular chain. -/
def standardAmbientSimplexChain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair d)).right.X d :=
  (TopCat.toSSet.obj (standardPuncturedPair d).fst).ιChainComplex
    (standardSingularSimplex d)

/-- The standard affine simplex, projected to the relative singular chain complex of
`(ℝ^d, ℝ^d ∖ {0})`. -/
def standardLocalChain (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (standardLocalRelativeChainComplex d).X d :=
  standardAmbientSimplexChain d ≫ standardLocalProjectionComponent d d

/-- A face of the standard simplex as an absolute singular chain. -/
def standardAmbientFaceChain (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).right.X n :=
  (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).ιChainComplex
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).δ i
      (standardSingularSimplex (n + 1)))

/-- A face of the standard simplex as a chain in the punctured subspace. -/
def standardSubspaceFaceChain (n : ℕ) (i : Fin (n + 2)) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.X n :=
  (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).snd).ιChainComplex
    (standardFaceSimplex n i)

lemma standardFaceChain_inclusion (n : ℕ) (i : Fin (n + 2)) :
    standardSubspaceFaceChain n i ≫
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).hom.f n =
    standardAmbientFaceChain n i := by
  change (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).snd).ιChainComplex
      (standardFaceSimplex n i) ≫
    (SSet.chainComplexMap
      (TopCat.toSSet.map (standardPuncturedPair (n + 1)).map)
      (ModuleCat.of ℚ ℚ)).f n = _
  rw [SSet.ι_chainComplexMap_f, standardFaceSimplex_map]
  rfl

lemma standardPairChain_projection (d k : ℕ) :
    ((chainPairFunctor ℚ).obj (standardPuncturedPair d)).hom.f k ≫
      standardLocalProjectionComponent d k = 0 := by
  have h := congrArg (fun f :
      ((chainPairFunctor ℚ).obj (standardPuncturedPair d)).left ⟶
        standardLocalRelativeChainComplex d => f.f k)
    (subspaceChainMap_relativeChainProjection ℚ (standardPuncturedPair d))
  change ((chainPairFunctor ℚ).obj (standardPuncturedPair d)).hom.f k ≫
    (relativeChainProjection ℚ (standardPuncturedPair d)).f k = 0 at h
  exact h

lemma standardFaceChain_projection (n : ℕ) (i : Fin (n + 2)) :
    standardAmbientFaceChain n i ≫ standardLocalProjectionComponent (n + 1) n = 0 := by
  rw [← standardFaceChain_inclusion, Category.assoc, standardPairChain_projection, comp_zero]

lemma standardAmbientSimplexChain_boundary (n : ℕ) :
    standardAmbientSimplexChain (n + 1) ≫
      ((chainPairFunctor ℚ).obj
        (standardPuncturedPair (n + 1))).right.d (n + 1) n =
    ∑ i : Fin (n + 2), (-1) ^ i.val • standardAmbientFaceChain n i := by
  change (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).ιChainComplex
      (standardSingularSimplex (n + 1)) ≫
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst).chainComplex
      (ModuleCat.of ℚ ℚ)).d (n + 1) n = _
  exact SSet.ιChainComplex_d
    (TopCat.toSSet.obj (standardPuncturedPair (n + 1)).fst)
    (ModuleCat.of ℚ ℚ) (standardSingularSimplex (n + 1))

lemma standardLocalProjectionComponent_comm (n : ℕ) :
    standardLocalProjectionComponent (n + 1) (n + 1) ≫
      (standardLocalRelativeChainComplex (n + 1)).d (n + 1) n =
    ((chainPairFunctor ℚ).obj
      (standardPuncturedPair (n + 1))).right.d (n + 1) n ≫
      standardLocalProjectionComponent (n + 1) n :=
  (relativeChainProjection ℚ (standardPuncturedPair (n + 1))).comm (n + 1) n

lemma standardLocalChain_boundary_succ (n : ℕ) :
    standardLocalChain (n + 1) ≫
      (standardLocalRelativeChainComplex (n + 1)).d (n + 1) n = 0 := by
  rw [standardLocalChain, Category.assoc, standardLocalProjectionComponent_comm,
    ← Category.assoc, standardAmbientSimplexChain_boundary, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro i _
  rw [Preadditive.zsmul_comp]
  change (-1) ^ i.val •
    (standardAmbientFaceChain n i ≫ standardLocalProjectionComponent (n + 1) n) = 0
  rw [standardFaceChain_projection]
  simp

lemma standardLocalChain_boundary (d : ℕ) :
    standardLocalChain d ≫
      (standardLocalRelativeChainComplex d).d d ((ComplexShape.down ℕ).next d) = 0 := by
  cases d with
  | zero => simp
  | succ n =>
      rw [ChainComplex.next_nat_succ]
      exact standardLocalChain_boundary_succ n

/-- The standard relative cycle represented by an affine simplex meeting the origin once. -/
def standardLocalCycle (d : ℕ) :
    ModuleCat.of ℚ ℚ ⟶ (standardLocalRelativeChainComplex d).cycles d :=
  (standardLocalRelativeChainComplex d).liftCycles (standardLocalChain d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary d)

/-- The canonical class represented by the standard affine local cycle in
`H_d(ℝ^d, ℝ^d ∖ {0}; ℚ)`. -/
def standardLocalClass (d : ℕ) :
    RelativeHomology ℚ (standardPuncturedPair d) d :=
  ((standardLocalCycle d ≫ (standardLocalRelativeChainComplex d).homologyπ d).hom) 1

lemma standardLocalCycle_inclusion (d : ℕ) :
    standardLocalCycle d ≫ (standardLocalRelativeChainComplex d).iCycles d =
      standardLocalChain d :=
  (standardLocalRelativeChainComplex d).liftCycles_i (standardLocalChain d)
    ((ComplexShape.down ℕ).next d) rfl (standardLocalChain_boundary d)

end AlgebraicTopology.Singular
