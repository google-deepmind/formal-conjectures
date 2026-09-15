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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.EuclideanLocalHomology
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularExcisionField
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularSubsetChains
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularStandardSimplexCone
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.StandardSphereAffineBoundary
public import Mathlib.Topology.Homotopy.Contractible

import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionPrism
import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularContractible
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.Bound
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# The affine sphere class in punctured Euclidean space

The recursive acyclic-filler construction is adapted from Paul Lezeau's
`SphereSixComplex/Topology/SingularAffineSubdivisionPrism.lean` in `sphere-six-complex`, commit
`4a00b63d81550972eb77cecb0eff28ef142e40a0`.

The affine boundary map sends the explicit simplicial fundamental cycle to the oriented
boundary cycle used in the standard Euclidean local class.  A finite open-facet cover of
punctured Euclidean space supplies a face-coherent carrier back to the standard simplicial
sphere.  An acyclic-carrier prism and the rational small-chain equivalence upgrade these maps to
a chain-homotopy equivalence.  Consequently the affine boundary map is an isomorphism on
homology, and the explicit punctured and positive-even-dimensional local classes generate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The affine barycentric coordinate indexed by the last vertex is normalized to zero; the
other coordinates are the ordinary coordinates on `ℝ^d`.  Only comparisons between these
coordinates are used below, so this common-translation normalization is canonical. -/
def standardExtendedCoordinate (d : ℕ) (i : Fin (d + 1))
    (x : StandardRealModel d) : ℝ :=
  Fin.lastCases 0 x i

@[simp]
lemma standardExtendedCoordinate_castSucc (d : ℕ) (i : Fin d)
    (x : StandardRealModel d) :
    standardExtendedCoordinate d (Fin.castSucc i) x = x i := by
  simp [standardExtendedCoordinate]

@[simp]
lemma standardExtendedCoordinate_last (d : ℕ) (x : StandardRealModel d) :
    standardExtendedCoordinate d (Fin.last d) x = 0 := by
  simp [standardExtendedCoordinate]

lemma standardExtendedCoordinate_standardAffineSimplex
    (d : ℕ) (i : Fin (d + 1)) (t : stdSimplex ℝ (Fin (d + 1))) :
    standardExtendedCoordinate d i (standardAffineSimplex d t) =
      t i - t (Fin.last d) := by
  cases i using Fin.lastCases with
  | last => simp
  | cast i => simp [standardAffineSimplex]

lemma stdSimplex_exists_pos {m : ℕ} (t : stdSimplex ℝ (Fin (m + 1))) :
    ∃ i, 0 < t i := by
  have hsum : (∑ i, (t : Fin (m + 1) → ℝ) i) ≠ 0 :=
    t.2.2.symm ▸ one_ne_zero
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨i, lt_of_le_of_ne (t.2.1 i) hi.symm⟩

lemma continuous_standardExtendedCoordinate (d : ℕ) (i : Fin (d + 1)) :
    Continuous (fun x : (standardPuncturedPair d).snd ↦
      standardExtendedCoordinate d i x.1) := by
  change Continuous (fun x : ({0}ᶜ : Set (StandardRealModel d)) ↦
    standardExtendedCoordinate d i x.1)
  cases i using Fin.lastCases with
  | last => simpa [standardExtendedCoordinate] using
      (continuous_const : Continuous (fun _ : ({0}ᶜ : Set (StandardRealModel d)) ↦ (0 : ℝ)))
  | cast i =>
      convert (continuous_apply i).comp continuous_subtype_val using 1
      funext x
      exact standardExtendedCoordinate_castSucc d i x.1

/-- The `i`th member of the finite facet cover consists of points for which the `i`th extended
coordinate is not maximal. -/
def standardPuncturedFacetCover (d : ℕ) (i : Fin (d + 1)) :
    Set ((standardPuncturedPair d).snd) :=
  {x | ∃ j : Fin (d + 1),
    standardExtendedCoordinate d i x.1 < standardExtendedCoordinate d j x.1}

lemma isOpen_standardPuncturedFacetCover (d : ℕ) (i : Fin (d + 1)) :
    IsOpen (standardPuncturedFacetCover d i) := by
  rw [show standardPuncturedFacetCover d i =
      ⋃ j : Fin (d + 1), {x | standardExtendedCoordinate d i x.1 <
        standardExtendedCoordinate d j x.1} by
        ext
        simp [standardPuncturedFacetCover]]
  exact isOpen_iUnion fun j ↦ isOpen_lt
    (continuous_standardExtendedCoordinate d i)
    (continuous_standardExtendedCoordinate d j)

/-- The nonmaximal-coordinate sets cover punctured coordinate space. -/
lemma iUnion_standardPuncturedFacetCover (d : ℕ) :
    ⋃ i, standardPuncturedFacetCover d i = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx : x.1 ≠ 0 := x.2
  obtain ⟨j, hj⟩ : ∃ j : Fin d, x.1 j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    exact hx (funext h)
  rcases lt_or_gt_of_ne hj with hjneg | hjpos
  · exact Set.mem_iUnion.mpr ⟨Fin.castSucc j, Fin.last d, by simpa using hjneg⟩
  · exact Set.mem_iUnion.mpr ⟨Fin.last d, Fin.castSucc j, by simpa using hjpos⟩

/-- No point belongs to every member of the facet cover. -/
lemma not_forall_mem_standardPuncturedFacetCover (d : ℕ)
    (x : (standardPuncturedPair d).snd) :
    ¬ ∀ i, x ∈ standardPuncturedFacetCover d i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin (d + 1) ↦ standardExtendedCoordinate d i x.1)
    Finset.univ_nonempty
  intro h
  obtain ⟨j, hj⟩ := h i
  exact (not_lt_of_ge (hi j (Finset.mem_univ j))) hj

/-- The coordinate vector whose extended coordinates are `-1` on `I` and `0` off `I`, up to
the common translation that makes the last extended coordinate zero. -/
def standardFacetIntersectionCenter (d : ℕ) (I : Finset (Fin (d + 1))) :
    StandardRealModel d :=
  fun j ↦ (if Fin.castSucc j ∈ I then (-1 : ℝ) else 0) -
    (if Fin.last d ∈ I then (-1 : ℝ) else 0)

lemma standardExtendedCoordinate_intersectionCenter (d : ℕ)
    (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    standardExtendedCoordinate d i (standardFacetIntersectionCenter d I) =
      (if i ∈ I then (-1 : ℝ) else 0) -
        (if Fin.last d ∈ I then (-1 : ℝ) else 0) := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [standardExtendedCoordinate]
  · simp [standardExtendedCoordinate, standardFacetIntersectionCenter]

lemma standardExtendedCoordinate_add_smul (d : ℕ) (i : Fin (d + 1))
    (a b : ℝ) (x y : StandardRealModel d) :
    standardExtendedCoordinate d i (a • x + b • y) =
      a * standardExtendedCoordinate d i x +
        b * standardExtendedCoordinate d i y := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [standardExtendedCoordinate]
  · simp [standardExtendedCoordinate]

/-- The intersection of a finite collection of facet-cover conditions, expressed in the
ambient coordinate vector space. -/
def standardPuncturedFacetIntersectionSet (d : ℕ)
    (I : Finset (Fin (d + 1))) : Set (StandardRealModel d) :=
  {x | ∀ i ∈ I, ∃ j : Fin (d + 1),
    standardExtendedCoordinate d i x < standardExtendedCoordinate d j x}

lemma standardFacetIntersectionCenter_mem (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I ≠ Finset.univ) :
    standardFacetIntersectionCenter d I ∈
      standardPuncturedFacetIntersectionSet d I := by
  classical
  obtain ⟨j, hj⟩ : Iᶜ.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun hc ↦ hI ((Finset.compl_eq_empty_iff I).1 hc)
  intro i hi
  refine ⟨j, ?_⟩
  rw [standardExtendedCoordinate_intersectionCenter,
    standardExtendedCoordinate_intersectionCenter]
  simp only [Finset.mem_compl] at hj
  by_cases hl : Fin.last d ∈ I <;> simp [hi, hj, hl]

lemma standardPuncturedFacetIntersectionSet_starConvex (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I ≠ Finset.univ) :
    StarConvex ℝ (standardFacetIntersectionCenter d I)
      (standardPuncturedFacetIntersectionSet d I) := by
  classical
  rw [starConvex_iff_segment_subset]
  intro y hy z hz
  rw [segment_eq_image] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  intro i hi
  by_cases hb0 : b = 0
  · subst b
    simpa using standardFacetIntersectionCenter_mem d I hI i hi
  · obtain ⟨j, hj⟩ := hy i hi
    refine ⟨j, ?_⟩
    rw [standardExtendedCoordinate_add_smul,
      standardExtendedCoordinate_add_smul]
    have hcenter : standardExtendedCoordinate d i
        (standardFacetIntersectionCenter d I) ≤
        standardExtendedCoordinate d j
          (standardFacetIntersectionCenter d I) := by
      rw [standardExtendedCoordinate_intersectionCenter,
        standardExtendedCoordinate_intersectionCenter]
      by_cases hjI : j ∈ I <;> simp [hi, hjI]
    have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
    have ha : 0 ≤ 1 - b := sub_nonneg.mpr hb.2
    nlinarith

lemma standardPuncturedFacetIntersectionSet_ne_zero (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I.Nonempty)
    {x : StandardRealModel d}
    (hx : x ∈ standardPuncturedFacetIntersectionSet d I) : x ≠ 0 := by
  obtain ⟨i, hi⟩ := hI
  obtain ⟨j, hj⟩ := hx i hi
  rintro rfl
  have hzeroCoord (k : Fin (d + 1)) :
      standardExtendedCoordinate d k (0 : StandardRealModel d) = 0 := by
    refine Fin.lastCases ?_ (fun l ↦ ?_) k <;> simp [standardExtendedCoordinate]
  rw [hzeroCoord i, hzeroCoord j] at hj
  exact (lt_self_iff_false 0).mp hj

/-- A proper nonempty intersection of facet-cover conditions, as a topological subspace of
the ambient coordinate vector space. -/
abbrev StandardPuncturedFacetIntersection (d : ℕ)
    (I : Finset (Fin (d + 1))) :=
  standardPuncturedFacetIntersectionSet d I

/-- Every proper intersection of facet-cover members is contractible. -/
lemma standardPuncturedFacetIntersection_contractibleSpace (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I ≠ Finset.univ) :
    ContractibleSpace (StandardPuncturedFacetIntersection d I) :=
  (standardPuncturedFacetIntersectionSet_starConvex d I hI).contractibleSpace
    ⟨standardFacetIntersectionCenter d I,
      standardFacetIntersectionCenter_mem d I hI⟩

/-- The same facet intersection, now presented as a subspace of punctured coordinate space. -/
def standardPuncturedFacetIntersectionSubspace (d : ℕ)
    (I : Finset (Fin (d + 1))) : Set ((standardPuncturedPair d).snd) :=
  {x | x.1 ∈ standardPuncturedFacetIntersectionSet d I}

/-- The ambient and nested-subspace presentations of a nonempty facet intersection are
homeomorphic. -/
def standardPuncturedFacetIntersectionHomeomorph (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I.Nonempty) :
    StandardPuncturedFacetIntersection d I ≃ₜ
      standardPuncturedFacetIntersectionSubspace d I where
  toFun x := ⟨⟨x.1,
    standardPuncturedFacetIntersectionSet_ne_zero d I hI x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A nonempty proper facet intersection is contractible in its nested-subspace presentation. -/
lemma standardPuncturedFacetIntersectionSubspace_contractibleSpace (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I.Nonempty) (hproper : I ≠ Finset.univ) :
    ContractibleSpace (standardPuncturedFacetIntersectionSubspace d I) := by
  let : ContractibleSpace (StandardPuncturedFacetIntersection d I) :=
    standardPuncturedFacetIntersection_contractibleSpace d I hproper
  exact (standardPuncturedFacetIntersectionHomeomorph d I hI).symm.contractibleSpace

/-- Inclusion of facet intersections, contravariant in their index sets. -/
def standardPuncturedFacetIntersectionMapOfSubset (d : ℕ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    TopCat.of (standardPuncturedFacetIntersectionSubspace d J) ⟶
      TopCat.of (standardPuncturedFacetIntersectionSubspace d I) :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, fun i hi ↦ x.2 i (hIJ hi)⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩

@[reassoc (attr := simp)]
lemma standardPuncturedFacetIntersectionMapOfSubset_comp_inclusion
    (d : ℕ) {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    standardPuncturedFacetIntersectionMapOfSubset d hIJ ≫
        topologicalSubsetInclusion (standardPuncturedPair d).snd
          (standardPuncturedFacetIntersectionSubspace d I) =
      topologicalSubsetInclusion (standardPuncturedPair d).snd
        (standardPuncturedFacetIntersectionSubspace d J) := by
  rfl

/-- Rational singular chains of a proper facet intersection are exact in positive degrees. -/
lemma standardPuncturedFacetIntersection_exactAt (d : ℕ)
    (I : Finset (Fin (d + 1))) (hI : I ≠ Finset.univ)
    (k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj
      (TopCat.of (StandardPuncturedFacetIntersection d I))).chainComplex
        (ModuleCat.of ℚ ℚ)).ExactAt k := by
  let : ContractibleSpace (StandardPuncturedFacetIntersection d I) :=
    standardPuncturedFacetIntersection_contractibleSpace d I hI
  exact AlgebraicTopology.singularChainComplex_exactAt_of_contractible
    ℚ (StandardPuncturedFacetIntersection d I) k hk

/-- Positive-degree integral singular homology of a nonempty proper facet intersection
vanishes. -/
lemma standardPuncturedFacetIntersection_integralHomology_isZero
    (d k : ℕ) (I : Finset (Fin (d + 1)))
    (hI : I.Nonempty) (hproper : I ≠ Finset.univ) (hk : k ≠ 0) :
    IsZero (((TopCat.toSSet.obj (TopCat.of
      (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
        (AddCommGrpCat.of ℤ)).homology k) := by
  change IsZero (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj
      (TopCat.of (standardPuncturedFacetIntersectionSubspace d I)))
  let : ContractibleSpace (standardPuncturedFacetIntersectionSubspace d I) :=
    standardPuncturedFacetIntersectionSubspace_contractibleSpace d I hI hproper
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (standardPuncturedFacetIntersectionSubspace d I)
  have hunit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat k (AddCommGrpCat.of ℤ) (TopCat.of Unit) hk
  let : Subsingleton (IntegralSingularHomology k Unit) :=
    AddCommGrpCat.subsingleton_of_isZero hunit
  let he := integralSingularHomologyEquivOfHomotopyEquiv k e
  let : Subsingleton
      (IntegralSingularHomology k
        (standardPuncturedFacetIntersectionSubspace d I)) :=
    ⟨fun x y ↦ he.injective (Subsingleton.elim _ _)⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- Integral singular chains of a nonempty proper facet intersection are exact in positive
degrees. -/
lemma standardPuncturedFacetIntersection_integralExactAt
    (d k : ℕ) (I : Finset (Fin (d + 1)))
    (hI : I.Nonempty) (hproper : I ≠ Finset.univ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj (TopCat.of
      (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
        (AddCommGrpCat.of ℤ)).ExactAt k := by
  let K := (TopCat.toSSet.obj (TopCat.of
    (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
      (AddCommGrpCat.of ℤ)
  rw [K.exactAt_iff_isZero_homology]
  exact standardPuncturedFacetIntersection_integralHomology_isZero
    d k I hI hproper hk

/-- Every positive-degree integral cycle in a nonempty proper facet intersection has a filler
in that intersection. -/
lemma exists_standardPuncturedFacetIntersection_integralCycleFiller
    (d n : ℕ) (I : Finset (Fin (d + 1)))
    (hI : I.Nonempty) (hproper : I ≠ Finset.univ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    ∃ p : AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
            (AddCommGrpCat.of ℤ)).X (n + 2),
      p ≫ ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z := by
  let K := (TopCat.toSSet.obj (TopCat.of
    (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
      (AddCommGrpCat.of ℤ)
  have hexact : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (i := n + 2) (j := n + 1) (k := n)
      (by simp) (by simp)).mp
        (standardPuncturedFacetIntersection_integralExactAt
          d (n + 1) I hI hproper (by lia))
  have hz1 : K.d (n + 1) n (z 1) = 0 := by
    simpa using ConcreteCategory.congr_hom hz 1
  obtain ⟨p, hp⟩ := (ShortComplex.ab_exact_iff _).mp hexact (z 1) hz1
  change K.X (n + 2) at p
  change K.d (n + 2) (n + 1) p = z 1 at hp
  refine ⟨AddCommGrpCat.asHom p, ?_⟩
  apply AddCommGrpCat.int_hom_ext
  change K.d (n + 2) (n + 1) ((AddCommGrpCat.asHom p) 1) = z 1
  rwa [AddCommGrpCat.asHom_hom_apply, one_zsmul]

/-- An integral singular zero-chain with zero component-wise augmentation bounds. -/
lemma exists_integralSingularZeroChain_filler
    (X : TopCat.{0})
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 0)
    (hz : z ≫ SSet.π₀.fromChainComplexXZero
      (TopCat.toSSet.obj X) (AddCommGrpCat.of ℤ) = 0) :
    ∃ p : AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 1,
      p ≫ ((TopCat.toSSet.obj X).chainComplex
        (AddCommGrpCat.of ℤ)).d 1 0 = z := by
  let K := (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)
  let q := SSet.π₀.fromChainComplexXZero
    (TopCat.toSSet.obj X) (AddCommGrpCat.of ℤ)
  let S : ShortComplex AddCommGrpCat :=
    ShortComplex.mk (K.d 1 0) q (SSet.π₀.d_fromChainComplexXZero
      (TopCat.toSSet.obj X) (AddCommGrpCat.of ℤ) 1)
  have hexact : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (SSet.isColimitCokernelCoforkChainComplexDOneZero
      (TopCat.toSSet.obj X) (AddCommGrpCat.of ℤ))
  have hz1 : q (z 1) = 0 := by
    simpa [q] using ConcreteCategory.congr_hom hz 1
  obtain ⟨p, hp⟩ := (S.ab_exact_iff).mp hexact (z 1) hz1
  change K.X 1 at p
  change K.d 1 0 p = z 1 at hp
  refine ⟨AddCommGrpCat.asHom p, ?_⟩
  apply AddCommGrpCat.int_hom_ext
  change K.d 1 0 ((AddCommGrpCat.asHom p) 1) = z 1
  rwa [AddCommGrpCat.asHom_hom_apply, one_zsmul]

/-- Cover indices through which a cover-small singular simplex factors. -/
def standardFacetCarrier (d : ℕ) {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).obj n) :
    Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦ x.1 ∈
      (SSet.Subcomplex.range (TopCat.toSSet.map
        (topologicalSubsetInclusion (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d i)))).obj n

lemma standardFacetCarrier_nonempty (d : ℕ) {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).obj n) :
    (standardFacetCarrier d x).Nonempty := by
  classical
  have hx := x.2
  rw [mem_coverSmallSingularSubcomplex_iff] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

lemma standardFacetCarrier_ne_univ (d : ℕ) {n : SimplexCategoryᵒᵖ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).obj n) :
    standardFacetCarrier d x ≠ Finset.univ := by
  classical
  intro hall
  let t : stdSimplex ℝ (Fin (n.unop.len + 1)) := stdSimplex.barycenter
  let p : (standardPuncturedPair d).snd :=
    ((standardPuncturedPair d).snd.toSSetObjEquiv n x.1) t
  apply not_forall_mem_standardPuncturedFacetCover d p
  intro i
  have hi : i ∈ standardFacetCarrier d x := by rw [hall]; simp
  rw [standardFacetCarrier, Finset.mem_filter] at hi
  exact (singularSimplex_mem_range_subset
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d i) x.1).mp hi.2 ⟨t, rfl⟩

lemma standardFacetCarrier_mono_map (d : ℕ)
    {m n : SimplexCategory} (f : m ⟶ n)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).obj
        (Opposite.op n)) :
    standardFacetCarrier d x ⊆
      standardFacetCarrier d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).map f.op x) := by
  classical
  intro i hi
  rw [standardFacetCarrier, Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, (SSet.Subcomplex.range (TopCat.toSSet.map
    (topologicalSubsetInclusion (standardPuncturedPair d).snd
      (standardPuncturedFacetCover d i)))).map f.op hi.2⟩

lemma standardFacetCarrier_mono_delta (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrier d x ⊆
      standardFacetCarrier d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d) : SSet).δ i x) :=
  standardFacetCarrier_mono_map d (SimplexCategory.δ i) x

/-- The singular simplex represented by `x`, on every simplicial degree, lies in the
intersection of the cover members containing `x`. -/
lemma standardFacetCarrierSource_image_subset_intersection
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (q : SimplexCategoryᵒᵖ) (y : (Δ[n] : SSet.{0}).obj q) :
    Set.range ((standardPuncturedPair d).snd.toSSetObjEquiv q
      ((SSet.yonedaEquiv.symm x.1).app q y)) ⊆
      standardPuncturedFacetIntersectionSubspace d
        (standardFacetCarrier d x) := by
  classical
  rintro _ ⟨t, rfl⟩ i hi
  rw [standardFacetCarrier, Finset.mem_filter] at hi
  apply (singularSimplex_mem_range_subset
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d i) x.1).mp hi.2
  let f : q.unop ⟶ SimplexCategory.mk n := SSet.stdSimplex.objEquiv y
  refine ⟨stdSimplex.map f t, ?_⟩
  have hy : y = SSet.stdSimplex.objEquiv.symm f :=
    (SSet.stdSimplex.objEquiv.symm_apply_apply y).symm
  rw [hy, SSet.yonedaEquiv_symm_app_objEquiv_symm,
    TopCat.toSSetObjEquiv_naturality_apply]

/-- The source singular simplex lifted to the contractible intersection assigned by its
carrier. -/
def standardFacetCarrierSourceIntersectionMap
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    (Δ[n] : SSet.{0}) ⟶
      TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x))) :=
  singularSimplicialMapLiftToSubset _ (standardPuncturedPair d).snd _
    (SSet.yonedaEquiv.symm x.1)
    (standardFacetCarrierSource_image_subset_intersection d x)

/-- The lifted source simplices are compatible with faces after restricting the assigned
facet intersection. -/
lemma standardFacetCarrierSourceIntersectionMap_delta
    (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierSourceIntersectionMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
        (standardFacetCarrier_mono_delta d n i x)) =
    SSet.stdSimplex.map (SimplexCategory.δ i) ≫
      standardFacetCarrierSourceIntersectionMap d x := by
  let hsub := standardFacetCarrier_mono_delta d n i x
  change standardFacetCarrier d x ⊆
    standardFacetCarrier d
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) at hsub
  change standardFacetCarrierSourceIntersectionMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d hsub) = _
  apply singularSimplicialMapToSubset_ext _ (standardPuncturedPair d).snd
    (standardPuncturedFacetIntersectionSubspace d (standardFacetCarrier d x))
  calc
    _ = standardFacetCarrierSourceIntersectionMap d
          ((coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d) : SSet).δ i x) ≫
        TopCat.toSSet.map
          (topologicalSubsetInclusion (standardPuncturedPair d).snd
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d
                ((coverSmallSingularSubcomplex
                  (standardPuncturedPair d).snd
                    (standardPuncturedFacetCover d) : SSet).δ i x)))) := by
          rw [Category.assoc, ← Functor.map_comp,
            standardPuncturedFacetIntersectionMapOfSubset_comp_inclusion]
    _ = SSet.yonedaEquiv.symm
          (((coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d) : SSet).δ i x).1) := by
          unfold standardFacetCarrierSourceIntersectionMap
          rw [singularSimplicialMapLiftToSubset_comp_inclusion]
    _ = SSet.stdSimplex.map (SimplexCategory.δ i) ≫
          SSet.yonedaEquiv.symm x.1 :=
      (SSet.stdSimplex.δ_comp_yonedaEquiv_symm x.1 i).symm
    _ = _ := by
      unfold standardFacetCarrierSourceIntersectionMap
      rw [Category.assoc,
        singularSimplicialMapLiftToSubset_comp_inclusion]

/-- Subdivision followed by last vertex, transported along the lifted source simplex. -/
def standardFacetCarrierSourceSubdivisionIntersectionMap
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶
      TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x))) :=
  simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫
    standardFacetCarrierSourceIntersectionMap d x

/-- The lifted subdivision--last-vertex source maps are compatible with faces. -/
lemma standardFacetCarrierSourceSubdivisionIntersectionMap_delta
    (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierSourceSubdivisionIntersectionMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
        (standardFacetCarrier_mono_delta d n i x)) =
    SimplexCategory.sd.{0}.map (SimplexCategory.δ i) ≫
      standardFacetCarrierSourceSubdivisionIntersectionMap d x := by
  unfold standardFacetCarrierSourceSubdivisionIntersectionMap
  rw [Category.assoc, standardFacetCarrierSourceIntersectionMap_delta, ← Category.assoc,
    ← simplexSubdivisionLastVertex.naturality, Category.assoc]

/-- Cover indices which contain the images of every vertex in `A`. -/
def standardFacetCarrierAtFace (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    Finset (Fin (d + 1)) := by
  classical
  exact Finset.univ.filter fun i ↦
    ∀ a ∈ A.finset,
      ((standardPuncturedPair d).snd.toSSetObjEquiv _ x.1)
        (stdSimplex.vertex a.down) ∈
        standardPuncturedFacetCover d i

lemma standardFacetCarrierAtFace_nonempty (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    (standardFacetCarrierAtFace d x A).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := standardFacetCarrier_nonempty d x
  rw [standardFacetCarrier, Finset.mem_filter] at hi
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun a _ ↦ ?_⟩⟩
  exact (singularSimplex_mem_range_subset
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d i) x.1).mp hi.2
    ⟨stdSimplex.vertex a.down, rfl⟩

lemma standardFacetCarrier_subset_atFace (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetCarrier d x ⊆ standardFacetCarrierAtFace d x A := by
  classical
  intro i hi
  rw [standardFacetCarrier, Finset.mem_filter] at hi
  rw [standardFacetCarrierAtFace, Finset.mem_filter]
  refine ⟨Finset.mem_univ i, fun a _ ↦ ?_⟩
  exact (singularSimplex_mem_range_subset
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d i) x.1).mp hi.2
    ⟨stdSimplex.vertex a.down, rfl⟩

lemma standardFacetCarrierAtFace_ne_univ (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetCarrierAtFace d x A ≠ Finset.univ := by
  classical
  intro hall
  obtain ⟨a, ha⟩ := A.nonempty
  let p : (standardPuncturedPair d).snd :=
    ((standardPuncturedPair d).snd.toSSetObjEquiv _ x.1)
      (stdSimplex.vertex a.down)
  apply not_forall_mem_standardPuncturedFacetCover d p
  intro i
  have hi : i ∈ standardFacetCarrierAtFace d x A := by rw [hall]; simp
  rw [standardFacetCarrierAtFace, Finset.mem_filter] at hi
  exact hi.2 a ha

lemma standardFacetCarrierAtFace_antitone (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    {A B : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))} (hAB : A ≤ B) :
    standardFacetCarrierAtFace d x B ⊆ standardFacetCarrierAtFace d x A := by
  classical
  intro i hi
  rw [standardFacetCarrierAtFace, Finset.mem_filter] at hi ⊢
  exact ⟨Finset.mem_univ i, fun a ha ↦ hi.2 a (hAB ha)⟩

/-- The complementary carrier is a nonempty proper set of vertices and grows with the face. -/
def standardFacetComplementCarrier (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    Finset (Fin (d + 1)) :=
  (standardFacetCarrierAtFace d x A)ᶜ

lemma standardFacetComplementCarrier_nonempty (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    (standardFacetComplementCarrier d x A).Nonempty := by
  classical
  rw [standardFacetComplementCarrier, Finset.nonempty_iff_ne_empty,
    ne_eq, Finset.compl_eq_empty_iff]
  exact standardFacetCarrierAtFace_ne_univ d x A

lemma standardFacetComplementCarrier_mono (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    Monotone (standardFacetComplementCarrier d x) := by
  classical
  intro A B hAB
  rw [standardFacetComplementCarrier, standardFacetComplementCarrier]
  exact Finset.compl_subset_compl.mpr
    (standardFacetCarrierAtFace_antitone d x hAB)

/-- The maximum vertex in the complementary carrier. -/
def standardFacetComplementCarrierMax (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) : Fin (d + 1) :=
  (standardFacetComplementCarrier d x A).max'
    (standardFacetComplementCarrier_nonempty d x A)

lemma standardFacetComplementCarrierMax_mono (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    Monotone (standardFacetComplementCarrierMax d x) := by
  intro A B hAB
  apply Finset.max'_le
  intro i hi
  exact Finset.le_max' _ i (standardFacetComplementCarrier_mono d x hAB hi)

/-- The largest vertex outside the face carrier, monotone as the face grows. -/
def standardFacetCarrierVertexOrderHom (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) →o
      ULift.{0} (Fin (d + 1)) where
  toFun A := ULift.up (standardFacetComplementCarrierMax d x A)
  monotone' _ _ hAB := standardFacetComplementCarrierMax_mono d x hAB

/-- The carrier map from the subdivision of a simplex to the standard simplex on cover
indices. -/
def standardFacetCarrierSimplexMap (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶ (Δ[d] : SSet.{0}) :=
  nerveMap (standardFacetCarrierVertexOrderHom d x).monotone.functor ≫
    (SSet.stdSimplex.isoNerve d).inv

@[simp]
lemma standardFacetCarrierSimplexMap_objEquiv_apply (d : ℕ) {n k : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)) _⦋k⦌)
    (r : Fin (k + 1)) :
    (SSet.stdSimplex.objEquiv
      ((standardFacetCarrierSimplexMap d x).app _ F)).toOrderHom r =
      ((standardFacetCarrierVertexOrderHom d x) (F.obj r)).down :=
  rfl

@[simp]
lemma standardFacetCarrierSimplexMap_apply (d : ℕ) {n k : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)) _⦋k⦌)
    (r : Fin (k + 1)) :
    ((standardFacetCarrierSimplexMap d x).app _ F) r =
      standardFacetComplementCarrierMax d x (F.obj r) :=
  standardFacetCarrierSimplexMap_objEquiv_apply d x F r

lemma standardFacetComplementCarrierMax_mem (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetComplementCarrierMax d x A ∈
      standardFacetComplementCarrier d x A :=
  Finset.max'_mem _ _

/-- Every simplex produced by the carrier misses a cover vertex and hence lies in the
simplicial boundary. -/
lemma standardFacetCarrierSimplexMap_mem_boundary (d : ℕ) {n k : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)) _⦋k⦌) :
    (standardFacetCarrierSimplexMap d x).app _ F ∈ (∂Δ[d]).obj
      (Opposite.op (SimplexCategory.mk k)) := by
  classical
  rw [SSet.mem_boundary_iff_notMem_range]
  let A := F.obj (Fin.last k)
  obtain ⟨j, hj⟩ := standardFacetCarrierAtFace_nonempty d x A
  refine ⟨j, ?_⟩
  rintro ⟨r, hr⟩
  have hmaxmem := standardFacetComplementCarrierMax_mem d x (F.obj r)
  have hjface : j ∈ standardFacetComplementCarrier d x (F.obj r) := by
    rw [← hr]
    simpa only [standardFacetCarrierSimplexMap_apply] using hmaxmem
  have hjmax : j ∈ standardFacetComplementCarrier d x A :=
    standardFacetComplementCarrier_mono d x (F.monotone (Fin.le_last r)) hjface
  exact (Finset.mem_compl.mp hjmax) hj

/-- The carrier map lifted to the simplicial boundary of the cover-index simplex. -/
def standardFacetCarrierBoundarySimplexMap (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶ (∂Δ[d] : SSet.{0}) :=
  SSet.Subcomplex.lift (standardFacetCarrierSimplexMap d x) (by
    rintro q y ⟨F, rfl⟩
    exact standardFacetCarrierSimplexMap_mem_boundary d x F)

@[reassoc (attr := simp)]
lemma standardFacetCarrierBoundarySimplexMap_comp_inclusion (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    standardFacetCarrierBoundarySimplexMap d x ≫ (∂Δ[d]).ι =
      standardFacetCarrierSimplexMap d x :=
  SSet.Subcomplex.lift_ι _ _

/-- Every vertex chosen by the carrier avoids every cover index containing the original
simplex. -/
lemma standardFacetCarrierBoundarySimplexMap_avoids_carrier
    (d : ℕ) {n k : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k)))
    (i : Fin (d + 1)) (hi : i ∈ standardFacetCarrier d x) :
    i ∉ Set.range
      ((standardFacetCarrierBoundarySimplexMap d x).app _ F).1 := by
  rintro ⟨r, hr⟩
  have himax := standardFacetComplementCarrierMax_mem d x (F.obj r)
  change standardFacetComplementCarrierMax d x (F.obj r) ∈
    (standardFacetCarrierAtFace d x (F.obj r))ᶜ at himax
  have hvalue := standardFacetCarrierSimplexMap_apply d x F r
  have hinclusion := congrArg
    (fun f : SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶
      (Δ[d] : SSet.{0}) ↦ f.app _ F)
    (standardFacetCarrierBoundarySimplexMap_comp_inclusion d x)
  change ((standardFacetCarrierBoundarySimplexMap d x).app _ F).1 =
    (standardFacetCarrierSimplexMap d x).app _ F at hinclusion
  rw [← hinclusion] at hvalue
  have heq : standardFacetComplementCarrierMax d x (F.obj r) = i :=
    hvalue.symm.trans hr
  apply Finset.mem_compl.mp himax
  rw [heq]
  exact standardFacetCarrier_subset_atFace d x (F.obj r) hi

/-- The vertex injection underlying a codimension-one face. -/
def standardFaceVertexOrderHom (n : ℕ) (i : Fin (n + 2)) :
    ULift.{0} (Fin (n + 1)) →o ULift.{0} (Fin (n + 2)) :=
  (SimplexCategory.toPartOrd.{0}.map (SimplexCategory.δ i)).hom

@[simp]
lemma standardFaceVertexOrderHom_apply (n : ℕ) (i : Fin (n + 2))
    (a : ULift.{0} (Fin (n + 1))) :
    standardFaceVertexOrderHom n i a = ULift.up (i.succAbove a.down) :=
  rfl

@[simp]
lemma coverSmallFacet_toSSetObjEquiv_delta_vertex (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌)
    (a : Fin (n + 1)) :
    ((standardPuncturedPair d).snd.toSSetObjEquiv _
      (((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x).1))
        (stdSimplex.vertex a) =
      ((standardPuncturedPair d).snd.toSSetObjEquiv _ x.1)
        (stdSimplex.vertex (i.succAbove a)) := by
  change ((standardPuncturedPair d).snd.toSSetObjEquiv _
      ((TopCat.toSSet.obj (standardPuncturedPair d).snd).δ i x.1))
        (stdSimplex.vertex a) = _
  rw [TopCat.toSSetObjEquiv_δ_apply, stdSimplex.map_vertex]

/-- Vertex carriers commute exactly with taking a codimension-one face. -/
lemma standardFacetCarrierAtFace_delta (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetCarrierAtFace d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) A =
      standardFacetCarrierAtFace d x
        (A.map (standardFaceVertexOrderHom n i)) := by
  classical
  ext j
  simp only [standardFacetCarrierAtFace, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h b hb
    rw [NonemptyFiniteChains.mem_map_iff] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    simpa only [standardFaceVertexOrderHom_apply, ULift.down_up,
      coverSmallFacet_toSSetObjEquiv_delta_vertex] using h a ha
  · intro h a ha
    have hb := h (standardFaceVertexOrderHom n i a)
      ((NonemptyFiniteChains.mem_map_iff A (standardFaceVertexOrderHom n i) _).mpr
        ⟨a, ha, rfl⟩)
    simpa only [standardFaceVertexOrderHom_apply, ULift.down_up,
      coverSmallFacet_toSSetObjEquiv_delta_vertex] using hb

lemma standardFacetComplementCarrierMax_delta (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetComplementCarrierMax d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) A =
      standardFacetComplementCarrierMax d x
        (A.map (standardFaceVertexOrderHom n i)) := by
  have hcomp : standardFacetComplementCarrier d
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) A =
      standardFacetComplementCarrier d x
        (A.map (standardFaceVertexOrderHom n i)) :=
    congrArg (fun s : Finset (Fin (d + 1)) ↦ sᶜ)
      (standardFacetCarrierAtFace_delta d n i x A)
  unfold standardFacetComplementCarrierMax
  simp only [hcomp]

/-- The carrier maps are natural for the codimension-one maps which occur in the chain
differential. -/
lemma standardFacetCarrierSimplexMap_delta (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    SimplexCategory.sd.{0}.map (SimplexCategory.δ i) ≫
        standardFacetCarrierSimplexMap d x =
      standardFacetCarrierSimplexMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) := by
  ext q F
  rcases q with ⟨⟨k⟩⟩
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  change (SSet.stdSimplex.objEquiv
      ((standardFacetCarrierSimplexMap d x).app _
        ((SimplexCategory.sd.{0}.map (SimplexCategory.δ i)).app _ F))).toOrderHom r =
    (SSet.stdSimplex.objEquiv
      ((standardFacetCarrierSimplexMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x)).app _ F)).toOrderHom r
  rw [standardFacetCarrierSimplexMap_objEquiv_apply,
    standardFacetCarrierSimplexMap_objEquiv_apply]
  change standardFacetComplementCarrierMax d x
      ((F.obj r).map (standardFaceVertexOrderHom n i)) =
    standardFacetComplementCarrierMax d
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x)
      (F.obj r)
  exact (standardFacetComplementCarrierMax_delta d n i x (F.obj r)).symm

lemma standardFacetCarrierBoundarySimplexMap_delta (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    SimplexCategory.sd.{0}.map (SimplexCategory.δ i) ≫
        standardFacetCarrierBoundarySimplexMap d x =
      standardFacetCarrierBoundarySimplexMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) := by
  apply (cancel_mono (∂Δ[d]).ι).mp
  simpa only [Category.assoc,
    standardFacetCarrierBoundarySimplexMap_comp_inclusion] using
      standardFacetCarrierSimplexMap_delta d n i x

/-- The signed barycentric carrier chain attached to one cover-small simplex. -/
def standardFacetCarrierSimplexChain (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    AddCommGrpCat.of ℤ ⟶ ((∂Δ[d] : SSet.{0}).chainComplex
      (AddCommGrpCat.of ℤ)).X n :=
  subdividedSimplexFundamentalChain n ≫
    (SSet.chainComplexMap (standardFacetCarrierBoundarySimplexMap d x)
      (AddCommGrpCat.of ℤ)).f n

/-- The degreewise carrier map on integral cover-small chains. -/
def standardFacetCarrierComponent (d n : ℕ) :
    (CoverSmallIntegralSingularChainComplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).X n ⟶
    ((∂Δ[d] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X n :=
  Sigma.desc (standardFacetCarrierSimplexChain d n)

@[reassoc (attr := simp)]
lemma iota_standardFacetCarrierComponent (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
        standardFacetCarrierComponent d n =
      standardFacetCarrierSimplexChain d n x :=
  Sigma.ι_desc _ _

lemma standardFacetCarrierComponent_comm_d (d n : ℕ) :
    standardFacetCarrierComponent d (n + 1) ≫
        ((∂Δ[d] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      (CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd
        (standardPuncturedFacetCover d)).d (n + 1) n ≫
          standardFacetCarrierComponent d n := by
  let K := (coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
  apply K.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_standardFacetCarrierComponent, standardFacetCarrierSimplexChain,
    Category.assoc, (SSet.chainComplexMap (standardFacetCarrierBoundarySimplexMap d x)
      (AddCommGrpCat.of ℤ)).comm (n + 1) n, ← Category.assoc,
    barycentricFundamentalBoundaryIdentity n, subdividedSimplexAlternatingFaceChain,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  dsimp only [K]
  simp_rw [Preadditive.zsmul_comp, iota_standardFacetCarrierComponent]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [standardFacetCarrierSimplexChain]
  have hcomp :
      (SSet.chainComplexMap
          (SimplexCategory.sd.{0}.map (SimplexCategory.δ i))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap (standardFacetCarrierBoundarySimplexMap d x)
          (AddCommGrpCat.of ℤ)).f n =
      (SSet.chainComplexMap
          (standardFacetCarrierBoundarySimplexMap d
            ((coverSmallSingularSubcomplex
              (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d) : SSet).δ i x))
          (AddCommGrpCat.of ℤ)).f n := by
    have hn := congrArg (fun f ↦ f.f n) (((SSet.chainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).congr_map (standardFacetCarrierBoundarySimplexMap_delta d n i x))
    rwa [Functor.map_comp] at hn
  simp only [hcomp]

/-- The integral finite-cover carrier chain map into the simplicial sphere. -/
def standardFacetCarrierChainMap (d : ℕ) :
    CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
      ((∂Δ[d] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)) :=
  ChainComplex.ofHom (standardFacetCarrierComponent d)
    (standardFacetCarrierComponent_comm_d d)

@[simp]
lemma standardFacetCarrierChainMap_f (d n : ℕ) :
    (standardFacetCarrierChainMap d).f n = standardFacetCarrierComponent d n :=
  rfl

/-- An affine boundary simplex is contained in the facet-cover member indexed by every vertex
which it misses. -/
lemma standardAffineBoundarySimplex_image_subset_facetCover
    (d n : ℕ) (y : (∂Δ[d] : SSet.{0}) _⦋n⦌)
    (i : Fin (d + 1)) (hi : i ∉ Set.range y.1) :
    Set.range ((standardPuncturedPair d).snd.toSSetObjEquiv _
      ((standardAffineBoundarySimplicialMap d).app _ y)) ⊆
        standardPuncturedFacetCover d i := by
  rintro _ ⟨t, rfl⟩
  let w := stdSimplex.map y.1 t
  obtain ⟨j, hj⟩ := stdSimplex_exists_pos w
  refine ⟨j, ?_⟩
  change standardExtendedCoordinate d i (standardAffineSimplex d w) <
    standardExtendedCoordinate d j (standardAffineSimplex d w)
  rw [standardExtendedCoordinate_standardAffineSimplex,
    standardExtendedCoordinate_standardAffineSimplex]
  have hzero : w i = 0 :=
    stdSimplex_map_apply_eq_zero_of_notMem_range y.1 t i hi
  linarith

/-- The affine realization of the carrier of a simplex lies in the intersection of all cover
members containing that simplex. -/
lemma standardFacetCarrierAffine_image_subset_intersection
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌)
    (q : SimplexCategoryᵒᵖ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj q) :
    Set.range ((standardPuncturedPair d).snd.toSSetObjEquiv q
      ((standardFacetCarrierBoundarySimplexMap d x ≫
        standardAffineBoundarySimplicialMap d).app q F)) ⊆
      standardPuncturedFacetIntersectionSubspace d
        (standardFacetCarrier d x) := by
  rintro _ ⟨t, rfl⟩ i hi
  exact standardAffineBoundarySimplex_image_subset_facetCover
    d q.unop.len ((standardFacetCarrierBoundarySimplexMap d x).app q F) i
      (standardFacetCarrierBoundarySimplexMap_avoids_carrier d x F i hi) ⟨t, rfl⟩

/-- The affine carrier map lifted to the contractible intersection assigned to its source
simplex. -/
def standardFacetCarrierAffineIntersectionMap
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶
      TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x))) :=
  singularSimplicialMapLiftToSubset _ (standardPuncturedPair d).snd _
    (standardFacetCarrierBoundarySimplexMap d x ≫
      standardAffineBoundarySimplicialMap d)
    (standardFacetCarrierAffine_image_subset_intersection d x)

/-- The lifted affine carrier maps are compatible with faces after restricting their assigned
facet intersections. -/
lemma standardFacetCarrierAffineIntersectionMap_delta
    (d n : ℕ) (i : Fin (n + 2))
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierAffineIntersectionMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
        (standardFacetCarrier_mono_delta d n i x)) =
    SimplexCategory.sd.{0}.map (SimplexCategory.δ i) ≫
      standardFacetCarrierAffineIntersectionMap d x := by
  let hsub := standardFacetCarrier_mono_delta d n i x
  change standardFacetCarrier d x ⊆
    standardFacetCarrier d
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) at hsub
  change standardFacetCarrierAffineIntersectionMap d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d hsub) = _
  apply singularSimplicialMapToSubset_ext _ (standardPuncturedPair d).snd
    (standardPuncturedFacetIntersectionSubspace d (standardFacetCarrier d x))
  calc
    _ = standardFacetCarrierAffineIntersectionMap d
          ((coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d) : SSet).δ i x) ≫
        TopCat.toSSet.map
          (topologicalSubsetInclusion (standardPuncturedPair d).snd
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d
                ((coverSmallSingularSubcomplex
                  (standardPuncturedPair d).snd
                    (standardPuncturedFacetCover d) : SSet).δ i x)))) := by
          rw [Category.assoc, ← Functor.map_comp,
            standardPuncturedFacetIntersectionMapOfSubset_comp_inclusion]
    _ = standardFacetCarrierBoundarySimplexMap d
          ((coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d) : SSet).δ i x) ≫
        standardAffineBoundarySimplicialMap d := by
          unfold standardFacetCarrierAffineIntersectionMap
          rw [singularSimplicialMapLiftToSubset_comp_inclusion]
    _ = SimplexCategory.sd.{0}.map (SimplexCategory.δ i) ≫
          standardFacetCarrierBoundarySimplexMap d x ≫
            standardAffineBoundarySimplicialMap d := by
      rw [← Category.assoc, standardFacetCarrierBoundarySimplexMap_delta]
    _ = _ := by
      unfold standardFacetCarrierAffineIntersectionMap
      rw [Category.assoc,
        singularSimplicialMapLiftToSubset_comp_inclusion]

/-- The difference, inside its assigned facet intersection, between the affine carrier and
subdivision followed by the last vertex of the original singular simplex. -/
def standardFacetCarrierIntersectionDiscrepancy
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).X n :=
  subdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap (standardFacetCarrierAffineIntersectionMap d x)
        (AddCommGrpCat.of ℤ)).f n -
    subdividedSimplexFundamentalChain n ≫
      (SSet.chainComplexMap
        (standardFacetCarrierSourceSubdivisionIntersectionMap d x)
        (AddCommGrpCat.of ℤ)).f n

/-- The alternating sum of face discrepancies, all restricted into the intersection assigned
to the original simplex. -/
def standardFacetCarrierIntersectionDiscrepancyFaces
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (standardFacetCarrierIntersectionDiscrepancy d n
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
          (standardFacetCarrier_mono_delta d n i x)))
        (AddCommGrpCat.of ℤ)).f n)

lemma standardFacetCarrierAffineIntersectionChain_boundary
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    (subdividedSimplexFundamentalChain (n + 1) ≫
        (SSet.chainComplexMap (standardFacetCarrierAffineIntersectionMap d x)
          (AddCommGrpCat.of ℤ)).f (n + 1)) ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      (subdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap
          (standardFacetCarrierAffineIntersectionMap d
            ((coverSmallSingularSubcomplex
              (standardPuncturedPair d).snd
                (standardPuncturedFacetCover d) : SSet).δ i x))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
            (standardFacetCarrier_mono_delta d n i x)))
          (AddCommGrpCat.of ℤ)).f n) := by
  rw [Category.assoc, (SSet.chainComplexMap (standardFacetCarrierAffineIntersectionMap d x)
    (AddCommGrpCat.of ℤ)).comm, ← Category.assoc, barycentricFundamentalBoundaryIdentity n,
    subdividedSimplexAlternatingFaceChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) •
    (subdividedSimplexFundamentalChain n ≫ k))
  have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).congr_map
    (standardFacetCarrierAffineIntersectionMap_delta d n i x)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun k ↦ k.f n) hmap.symm

lemma standardFacetCarrierSourceIntersectionChain_boundary
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    (subdividedSimplexFundamentalChain (n + 1) ≫
        (SSet.chainComplexMap
          (standardFacetCarrierSourceSubdivisionIntersectionMap d x)
          (AddCommGrpCat.of ℤ)).f (n + 1)) ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      (subdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap
          (standardFacetCarrierSourceSubdivisionIntersectionMap d
            ((coverSmallSingularSubcomplex
              (standardPuncturedPair d).snd
                (standardPuncturedFacetCover d) : SSet).δ i x))
          (AddCommGrpCat.of ℤ)).f n ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
            (standardFacetCarrier_mono_delta d n i x)))
          (AddCommGrpCat.of ℤ)).f n) := by
  rw [Category.assoc, (SSet.chainComplexMap
    (standardFacetCarrierSourceSubdivisionIntersectionMap d x)
    (AddCommGrpCat.of ℤ)).comm, ← Category.assoc, barycentricFundamentalBoundaryIdentity n,
    subdividedSimplexAlternatingFaceChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) •
    (subdividedSimplexFundamentalChain n ≫ k))
  have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).congr_map
    (standardFacetCarrierSourceSubdivisionIntersectionMap_delta d n i x)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun k ↦ k.f n) hmap.symm

/-- The discrepancy boundary is the alternating sum of the restricted face discrepancies. -/
lemma standardFacetCarrierIntersectionDiscrepancy_boundary
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierIntersectionDiscrepancy d (n + 1) x ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n =
      standardFacetCarrierIntersectionDiscrepancyFaces d n x := by
  rw [standardFacetCarrierIntersectionDiscrepancy, Preadditive.sub_comp,
    standardFacetCarrierAffineIntersectionChain_boundary,
    standardFacetCarrierSourceIntersectionChain_boundary,
    standardFacetCarrierIntersectionDiscrepancyFaces, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [standardFacetCarrierIntersectionDiscrepancy]
  simp only [smul_sub, Preadditive.sub_comp, Category.assoc]

/-- The chain map which includes an assigned carrier intersection into punctured coordinate
space. -/
def standardFacetCarrierIntersectionChainInclusion
    (d : ℕ) {n : ℕ}
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
          (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map
      (topologicalSubsetInclusion (standardPuncturedPair d).snd
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x))))
    (AddCommGrpCat.of ℤ)

/-- The carrier discrepancy, now regarded as a chain in the ambient punctured space. -/
def standardFacetCarrierDiscrepancySimplexChain
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (AddCommGrpCat.of ℤ)).X n :=
  standardFacetCarrierIntersectionDiscrepancy d n x ≫
    (standardFacetCarrierIntersectionChainInclusion d x).f n

/-- The degreewise ambient discrepancy operator on cover-small integral chains. -/
def standardFacetCarrierDiscrepancyComponent (d n : ℕ) :
    (CoverSmallIntegralSingularChainComplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).X n ⟶
    ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
      (AddCommGrpCat.of ℤ)).X n :=
  Sigma.desc (standardFacetCarrierDiscrepancySimplexChain d n)

@[reassoc (attr := simp)]
lemma iota_standardFacetCarrierDiscrepancyComponent
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
      standardFacetCarrierDiscrepancyComponent d n =
    standardFacetCarrierDiscrepancySimplexChain d n x :=
  Sigma.ι_desc _ _

lemma standardFacetCarrierDiscrepancyFaces_comp_inclusion
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierIntersectionDiscrepancyFaces d n x ≫
        (standardFacetCarrierIntersectionChainInclusion d x).f n =
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
        (CoverSmallIntegralSingularChainComplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d)).d (n + 1) n ≫
          standardFacetCarrierDiscrepancyComponent d n := by
  rw [standardFacetCarrierIntersectionDiscrepancyFaces,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_standardFacetCarrierDiscrepancyComponent,
    standardFacetCarrierDiscrepancySimplexChain]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) • k)
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hsset := TopCat.toSSet.congr_map
    (standardPuncturedFacetIntersectionMapOfSubset_comp_inclusion d
      (standardFacetCarrier_mono_delta d n i x))
  have hchain :
      SSet.chainComplexMap
          (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
            (standardFacetCarrier_mono_delta d n i x)))
          (AddCommGrpCat.of ℤ) ≫
        standardFacetCarrierIntersectionChainInclusion d x =
      standardFacetCarrierIntersectionChainInclusion d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d) : SSet).δ i x) := by
    rw [Functor.map_comp] at hsset
    change F.map _ ≫ F.map _ = F.map _
    rw [← Functor.map_comp]
    exact F.congr_map hsset
  have hn := congrArg (fun k ↦ k.f n) hchain
  simpa only [HomologicalComplex.comp_f, Category.assoc] using congrArg
    (fun k ↦ standardFacetCarrierIntersectionDiscrepancy d n
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d) : SSet).δ i x) ≫ k) hn

/-- The ambient carrier discrepancy commutes with the singular differential. -/
lemma standardFacetCarrierDiscrepancyComponent_comm_d (d n : ℕ) :
    standardFacetCarrierDiscrepancyComponent d (n + 1) ≫
        ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n =
      (CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d)).d (n + 1) n ≫
        standardFacetCarrierDiscrepancyComponent d n := by
  apply (coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd
      (standardPuncturedFacetCover d) : SSet).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_standardFacetCarrierDiscrepancyComponent,
    standardFacetCarrierDiscrepancySimplexChain, Category.assoc,
    (standardFacetCarrierIntersectionChainInclusion d x).comm, ← Category.assoc,
    standardFacetCarrierIntersectionDiscrepancy_boundary]
  exact standardFacetCarrierDiscrepancyFaces_comp_inclusion d n x

/-- The carrier discrepancy as a chain map from cover-small chains to ambient singular
chains. -/
def standardFacetCarrierDiscrepancyChainMap (d : ℕ) :
    CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
      (TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (AddCommGrpCat.of ℤ) :=
  ChainComplex.ofHom (standardFacetCarrierDiscrepancyComponent d)
    (standardFacetCarrierDiscrepancyComponent_comm_d d)

@[simp]
lemma standardFacetCarrierDiscrepancyChainMap_f (d n : ℕ) :
    (standardFacetCarrierDiscrepancyChainMap d).f n =
      standardFacetCarrierDiscrepancyComponent d n :=
  rfl

/-- A family of local carrier prisms, one degree-raising chain for every cover-small
simplex. -/
abbrev StandardFacetCarrierPrismFamily (d : ℕ) :=
  ∀ (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌),
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).X (n + 1)

/-- The alternating sum of the already constructed face prisms, restricted into the carrier
intersection assigned to the original simplex. -/
def standardFacetCarrierPrismFaces
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).X (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    (P n ((coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd
        (standardPuncturedFacetCover d) : SSet).δ i x) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
          (standardFacetCarrier_mono_delta d n i x)))
        (AddCommGrpCat.of ℤ)).f (n + 1))

/-- One local prism chain, included into ambient punctured coordinate space. -/
def standardFacetCarrierPrismSimplexChain
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (AddCommGrpCat.of ℤ)).X (n + 1) :=
  P n x ≫ (standardFacetCarrierIntersectionChainInclusion d x).f (n + 1)

/-- The global degree-raising carrier-prism operator induced by local prism chains. -/
def standardFacetCarrierPrismComponent
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ) :
    (CoverSmallIntegralSingularChainComplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).X n ⟶
    ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
      (AddCommGrpCat.of ℤ)).X (n + 1) :=
  Sigma.desc (standardFacetCarrierPrismSimplexChain d P n)

@[reassoc (attr := simp)]
lemma iota_standardFacetCarrierPrismComponent
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
      standardFacetCarrierPrismComponent d P n =
    standardFacetCarrierPrismSimplexChain d P n x :=
  Sigma.ι_desc _ _

lemma standardFacetCarrierPrismFaces_comp_inclusion
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierPrismFaces d P n x ≫
        (standardFacetCarrierIntersectionChainInclusion d x).f (n + 1) =
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
        (CoverSmallIntegralSingularChainComplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d)).d (n + 1) n ≫
          standardFacetCarrierPrismComponent d P n := by
  rw [standardFacetCarrierPrismFaces, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp,
    iota_standardFacetCarrierPrismComponent,
    standardFacetCarrierPrismSimplexChain]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  apply congrArg (fun k ↦ ((-1 : ℤ) ^ i.val) • k)
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hsset := TopCat.toSSet.congr_map
    (standardPuncturedFacetIntersectionMapOfSubset_comp_inclusion d
      (standardFacetCarrier_mono_delta d n i x))
  have hchain :
      SSet.chainComplexMap
          (TopCat.toSSet.map (standardPuncturedFacetIntersectionMapOfSubset d
            (standardFacetCarrier_mono_delta d n i x)))
          (AddCommGrpCat.of ℤ) ≫
        standardFacetCarrierIntersectionChainInclusion d x =
      standardFacetCarrierIntersectionChainInclusion d
        ((coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d) : SSet).δ i x) := by
    rw [Functor.map_comp] at hsset
    change F.map _ ≫ F.map _ = F.map _
    rw [← Functor.map_comp]
    exact F.congr_map hsset
  have hn := congrArg (fun k ↦ k.f (n + 1)) hchain
  simpa only [HomologicalComplex.comp_f, Category.assoc] using congrArg
    (fun k ↦ P n
      ((coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d) : SSet).δ i x) ≫ k) hn

/-- Local degree-zero prism equations assemble into the ambient homotopy equation. -/
lemma standardFacetCarrierPrismComponent_boundary_zero
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d)
    (h : ∀ x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌,
      standardFacetCarrierIntersectionDiscrepancy d 0 x =
        P 0 x ≫
          ((TopCat.toSSet.obj (TopCat.of
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x)))).chainComplex
                (AddCommGrpCat.of ℤ)).d 1 0) :
    (standardFacetCarrierDiscrepancyChainMap d).f 0 =
      standardFacetCarrierPrismComponent d P 0 ≫
        ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0 := by
  apply (coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd
      (standardPuncturedFacetCover d) : SSet).chainComplex_hom_ext
  intro x
  rw [standardFacetCarrierDiscrepancyChainMap_f,
    iota_standardFacetCarrierDiscrepancyComponent,
    standardFacetCarrierDiscrepancySimplexChain, ← Category.assoc,
    iota_standardFacetCarrierPrismComponent, standardFacetCarrierPrismSimplexChain,
    Category.assoc, (standardFacetCarrierIntersectionChainInclusion d x).comm,
    ← Category.assoc, h]

/-- Local positive-degree prism equations assemble into the ambient homotopy equation. -/
lemma standardFacetCarrierPrismComponent_boundary_succ
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (h : ∀ x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌,
      standardFacetCarrierIntersectionDiscrepancy d (n + 1) x =
        P (n + 1) x ≫
            ((TopCat.toSSet.obj (TopCat.of
              (standardPuncturedFacetIntersectionSubspace d
                (standardFacetCarrier d x)))).chainComplex
                  (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
          standardFacetCarrierPrismFaces d P n x) :
    (standardFacetCarrierDiscrepancyChainMap d).f (n + 1) =
      (CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd
          (standardPuncturedFacetCover d)).d (n + 1) n ≫
          standardFacetCarrierPrismComponent d P n +
        standardFacetCarrierPrismComponent d P (n + 1) ≫
          ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) := by
  apply (coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd
      (standardPuncturedFacetCover d) : SSet).chainComplex_hom_ext
  intro x
  simp only [Preadditive.comp_add]
  rw [standardFacetCarrierDiscrepancyChainMap_f,
    iota_standardFacetCarrierDiscrepancyComponent,
    standardFacetCarrierDiscrepancySimplexChain, h, add_comm
    (P (n + 1) x ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1))
    (standardFacetCarrierPrismFaces d P n x), Preadditive.add_comp]
  apply congrArg₂ (fun a b ↦ a + b)
  · exact standardFacetCarrierPrismFaces_comp_inclusion d P n x
  · rw [← Category.assoc, iota_standardFacetCarrierPrismComponent,
      standardFacetCarrierPrismSimplexChain]
    calc
      (P (n + 1) x ≫
          ((TopCat.toSSet.obj (TopCat.of
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x)))).chainComplex
                (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) ≫
            (standardFacetCarrierIntersectionChainInclusion d x).f (n + 1) =
        P (n + 1) x ≫
          (((TopCat.toSSet.obj (TopCat.of
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x)))).chainComplex
                (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) ≫
            (standardFacetCarrierIntersectionChainInclusion d x).f (n + 1)) :=
          Category.assoc _ _ _
      _ = P (n + 1) x ≫
          ((standardFacetCarrierIntersectionChainInclusion d x).f (n + 2) ≫
            ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1)) := by
            rw [(standardFacetCarrierIntersectionChainInclusion d x).comm]
      _ = (P (n + 1) x ≫
          (standardFacetCarrierIntersectionChainInclusion d x).f (n + 2)) ≫
            ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) :=
          (Category.assoc _ _ _).symm

/-- The degree-zero discrepancy has zero component-wise augmentation in its contractible
carrier intersection. -/
lemma standardFacetCarrierIntersectionDiscrepancy_zero_augmentation
    (d : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌) :
    standardFacetCarrierIntersectionDiscrepancy d 0 x ≫
      SSet.π₀.fromChainComplexXZero
        (TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x))))
        (AddCommGrpCat.of ℤ) = 0 := by
  let I := standardFacetCarrier d x
  have hI : I.Nonempty := standardFacetCarrier_nonempty d x
  have hproper : I ≠ Finset.univ := standardFacetCarrier_ne_univ d x
  let : ContractibleSpace
      (standardPuncturedFacetIntersectionSubspace d I) :=
    standardPuncturedFacetIntersectionSubspace_contractibleSpace d I hI hproper
  rw [standardFacetCarrierIntersectionDiscrepancy, Preadditive.sub_comp,
    subdividedSimplexFundamentalChain]
  simp
  have heq :
      SSet.π₀.mk
        ((standardFacetCarrierAffineIntersectionMap d x).app _
          (permutationMaximalFlagSimplex (1 : Equiv.Perm (Fin 1)))) =
      SSet.π₀.mk
        ((standardFacetCarrierSourceSubdivisionIntersectionMap d x).app _
          (permutationMaximalFlagSimplex (1 : Equiv.Perm (Fin 1)))) :=
    Subsingleton.elim _ _
  rw [heq, sub_self]

/-- The degree-zero local discrepancy admits a one-chain filler in its carrier
intersection. -/
lemma exists_standardFacetCarrierIntersectionPrism_zero
    (d : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌) :
    ∃ p : AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x)))).chainComplex
              (AddCommGrpCat.of ℤ)).X 1,
      p ≫ ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d 1 0 =
        standardFacetCarrierIntersectionDiscrepancy d 0 x :=
  exists_integralSingularZeroChain_filler
    (TopCat.of (standardPuncturedFacetIntersectionSubspace d
      (standardFacetCarrier d x)))
    (standardFacetCarrierIntersectionDiscrepancy d 0 x)
    (standardFacetCarrierIntersectionDiscrepancy_zero_augmentation d x)

/-- The local residual left after subtracting the already constructed face prisms. -/
def standardFacetCarrierPrismResidual
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).X (n + 1) :=
  standardFacetCarrierIntersectionDiscrepancy d (n + 1) x -
    standardFacetCarrierPrismFaces d P n x

lemma standardFacetCarrierPrismResidual_comp_inclusion
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierPrismResidual d P n x ≫
        (standardFacetCarrierIntersectionChainInclusion d x).f (n + 1) =
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
          (standardFacetCarrierDiscrepancyChainMap d).f (n + 1) -
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet).ιChainComplex x ≫
          (CoverSmallIntegralSingularChainComplex
            (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d)).d (n + 1) n ≫
            standardFacetCarrierPrismComponent d P n := by
  rw [standardFacetCarrierPrismResidual, Preadditive.sub_comp]
  apply congrArg₂ (fun a b ↦ a - b)
  · rw [standardFacetCarrierDiscrepancyChainMap_f,
      iota_standardFacetCarrierDiscrepancyComponent,
      standardFacetCarrierDiscrepancySimplexChain]
  · exact standardFacetCarrierPrismFaces_comp_inclusion d P n x

set_option linter.style.haveILetI false in
/-- If the local prism equation holds one degree lower, the next local residual is a cycle.
This is the acyclic-carrier cancellation step. -/
lemma standardFacetCarrierPrismResidual_cycle
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (hzero : n = 0 →
      ∀ x : (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌,
        standardFacetCarrierIntersectionDiscrepancy d 0 x =
          P 0 x ≫
            ((TopCat.toSSet.obj (TopCat.of
              (standardPuncturedFacetIntersectionSubspace d
                (standardFacetCarrier d x)))).chainComplex
                  (AddCommGrpCat.of ℤ)).d 1 0)
    (hsucc : ∀ k, n = k + 1 →
      ∀ x : (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋k + 1⦌,
        standardFacetCarrierIntersectionDiscrepancy d (k + 1) x =
          P (k + 1) x ≫
              ((TopCat.toSSet.obj (TopCat.of
                (standardPuncturedFacetIntersectionSubspace d
                  (standardFacetCarrier d x)))).chainComplex
                    (AddCommGrpCat.of ℤ)).d (k + 2) (k + 1) +
            standardFacetCarrierPrismFaces d P k x)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierPrismResidual d P n x ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
  let I := standardFacetCarrierIntersectionChainInclusion d x
  haveI : Mono (I.f n) := by
    dsimp [I, standardFacetCarrierIntersectionChainInclusion]
    exact singularSubsetIntegralChainInclusionComponent_mono
      (standardPuncturedPair d).snd
      (standardPuncturedFacetIntersectionSubspace d
        (standardFacetCarrier d x)) n
  apply (cancel_mono (I.f n)).mp
  rw [zero_comp]
  calc
    (standardFacetCarrierPrismResidual d P n x ≫
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x)))).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n) ≫ I.f n =
      standardFacetCarrierPrismResidual d P n x ≫
        (((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x)))).chainComplex
              (AddCommGrpCat.of ℤ)).d (n + 1) n ≫ I.f n) :=
        Category.assoc _ _ _
    _ = standardFacetCarrierPrismResidual d P n x ≫
        (I.f (n + 1) ≫
          ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n) := by
      rw [I.comm]
    _ = (standardFacetCarrierPrismResidual d P n x ≫ I.f (n + 1)) ≫
        ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n :=
      (Category.assoc _ _ _).symm
  rw [standardFacetCarrierPrismResidual_comp_inclusion, Preadditive.sub_comp, Category.assoc,
    (standardFacetCarrierDiscrepancyChainMap d).comm, Category.assoc, Category.assoc]
  cases n with
  | zero =>
      have hprev := standardFacetCarrierPrismComponent_boundary_zero d P
        (hzero rfl)
      rw [hprev]
      simp only [sub_self]
  | succ k =>
      have hprev := standardFacetCarrierPrismComponent_boundary_succ d P k
        (hsucc k rfl)
      rw [hprev, Preadditive.comp_add, ← Category.assoc,
        (CoverSmallIntegralSingularChainComplex
          (standardPuncturedPair d).snd
            (standardPuncturedFacetCover d)).d_comp_d]
      simp only [zero_comp, zero_add, sub_self]

/-- Every positive-degree residual has a filler in its proper contractible carrier
intersection. -/
lemma exists_standardFacetCarrierPrismResidual_filler
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (hzero : n = 0 →
      ∀ x : (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌,
        standardFacetCarrierIntersectionDiscrepancy d 0 x =
          P 0 x ≫
            ((TopCat.toSSet.obj (TopCat.of
              (standardPuncturedFacetIntersectionSubspace d
                (standardFacetCarrier d x)))).chainComplex
                  (AddCommGrpCat.of ℤ)).d 1 0)
    (hsucc : ∀ k, n = k + 1 →
      ∀ x : (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋k + 1⦌,
        standardFacetCarrierIntersectionDiscrepancy d (k + 1) x =
          P (k + 1) x ≫
              ((TopCat.toSSet.obj (TopCat.of
                (standardPuncturedFacetIntersectionSubspace d
                  (standardFacetCarrier d x)))).chainComplex
                    (AddCommGrpCat.of ℤ)).d (k + 2) (k + 1) +
            standardFacetCarrierPrismFaces d P k x)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    ∃ p : AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x)))).chainComplex
              (AddCommGrpCat.of ℤ)).X (n + 2),
      p ≫ ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) =
        standardFacetCarrierPrismResidual d P n x := by
  have hI : (standardFacetCarrier d x).Nonempty :=
    standardFacetCarrier_nonempty d x
  have hproper : standardFacetCarrier d x ≠ Finset.univ :=
    standardFacetCarrier_ne_univ d x
  exact exists_standardPuncturedFacetIntersection_integralCycleFiller
    d n (standardFacetCarrier d x) hI hproper
    (standardFacetCarrierPrismResidual d P n x)
    (standardFacetCarrierPrismResidual_cycle d P n hzero hsucc x)

/-- The local acyclic-carrier prism equation in one degree. -/
def StandardFacetCarrierPrismEquation
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) : ℕ → Prop :=
  fun n ↦ match n with
  | 0 => ∀ x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌,
      standardFacetCarrierIntersectionDiscrepancy d 0 x =
        P 0 x ≫
          ((TopCat.toSSet.obj (TopCat.of
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x)))).chainComplex
                (AddCommGrpCat.of ℤ)).d 1 0
  | n + 1 => ∀ x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌,
      standardFacetCarrierIntersectionDiscrepancy d (n + 1) x =
        P (n + 1) x ≫
            ((TopCat.toSSet.obj (TopCat.of
              (standardPuncturedFacetIntersectionSubspace d
                (standardFacetCarrier d x)))).chainComplex
                  (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) +
          standardFacetCarrierPrismFaces d P n x

lemma standardFacetCarrierPrismResidual_cycle_of_equation
    (d : ℕ) (P : StandardFacetCarrierPrismFamily d) (n : ℕ)
    (h : StandardFacetCarrierPrismEquation d P n)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierPrismResidual d P n x ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d
          (standardFacetCarrier d x)))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 := by
  apply standardFacetCarrierPrismResidual_cycle d P n
  · rintro rfl
    exact h
  · rintro k rfl
    exact h

/-- A total selected filler for a positive-degree cycle in a proper facet intersection.  It
returns zero when its input is not a cycle, so it can be used in a structural recursion whose
cycle proof is established afterwards. -/
def standardPuncturedFacetIntersectionIntegralTotalCycleFiller
    (d n : ℕ) (I : Finset (Fin (d + 1)))
    (hI : I.Nonempty) (hproper : I ≠ Finset.univ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1)) :
    AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 2) := by
  classical
  exact if hz : z ≫
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
            (AddCommGrpCat.of ℤ)).d (n + 1) n = 0 then
      Classical.choose
        (exists_standardPuncturedFacetIntersection_integralCycleFiller
          d n I hI hproper z hz)
    else 0

/-- The total selected filler has the prescribed boundary whenever its input is a cycle. -/
lemma standardPuncturedFacetIntersectionIntegralTotalCycleFiller_boundary
    (d n : ℕ) (I : Finset (Fin (d + 1)))
    (hI : I.Nonempty) (hproper : I ≠ Finset.univ)
    (z : AddCommGrpCat.of ℤ ⟶
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).X (n + 1))
    (hz : z ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 1) n = 0) :
    standardPuncturedFacetIntersectionIntegralTotalCycleFiller
        d n I hI hproper z ≫
      ((TopCat.toSSet.obj (TopCat.of
        (standardPuncturedFacetIntersectionSubspace d I))).chainComplex
          (AddCommGrpCat.of ℤ)).d (n + 2) (n + 1) = z := by
  rw [standardPuncturedFacetIntersectionIntegralTotalCycleFiller, dif_pos hz]
  exact Classical.choose_spec
    (exists_standardPuncturedFacetIntersection_integralCycleFiller
      d n I hI hproper z hz)

/-- The canonical local acyclic-carrier prism, recursively obtained by filling the discrepancy
left after the prisms on all faces. -/
def standardFacetCarrierPrism (d n : ℕ) :
    ∀ (x : (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌),
      AddCommGrpCat.of ℤ ⟶
        ((TopCat.toSSet.obj (TopCat.of
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x)))).chainComplex
              (AddCommGrpCat.of ℤ)).X (n + 1) :=
  match n with
  | 0 => fun x ↦ Classical.choose
        (exists_standardFacetCarrierIntersectionPrism_zero d x)
  | n + 1 => fun x ↦
        standardPuncturedFacetIntersectionIntegralTotalCycleFiller
          d n (standardFacetCarrier d x)
          (standardFacetCarrier_nonempty d x)
          (standardFacetCarrier_ne_univ d x)
          (standardFacetCarrierIntersectionDiscrepancy d (n + 1) x -
            ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
              (standardFacetCarrierPrism d n
                  ((coverSmallSingularSubcomplex
                    (standardPuncturedPair d).snd
                      (standardPuncturedFacetCover d) : SSet).δ i x) ≫
                (SSet.chainComplexMap
                  (TopCat.toSSet.map
                    (standardPuncturedFacetIntersectionMapOfSubset d
                      (standardFacetCarrier_mono_delta d n i x)))
                  (AddCommGrpCat.of ℤ)).f (n + 1)))
termination_by n

@[simp]
lemma standardFacetCarrierPrism_zero
    (d : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋0⦌) :
    standardFacetCarrierPrism d 0 x =
      Classical.choose
        (exists_standardFacetCarrierIntersectionPrism_zero d x) :=
  by simp [standardFacetCarrierPrism]

/-- The successor prism is the total filler of the local residual. -/
lemma standardFacetCarrierPrism_succ
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n + 1⦌) :
    standardFacetCarrierPrism d (n + 1) x =
      standardPuncturedFacetIntersectionIntegralTotalCycleFiller
        d n (standardFacetCarrier d x)
        (standardFacetCarrier_nonempty d x)
        (standardFacetCarrier_ne_univ d x)
        (standardFacetCarrierPrismResidual d
          (standardFacetCarrierPrism d) n x) := by
  simp [standardFacetCarrierPrism,
    standardFacetCarrierPrismResidual, standardFacetCarrierPrismFaces]

/-- The recursively selected local prisms satisfy the complete acyclic-carrier boundary
equation in every degree. -/
lemma standardFacetCarrierPrism_equation (d n : ℕ) :
    StandardFacetCarrierPrismEquation d (standardFacetCarrierPrism d) n := by
  induction n with
  | zero =>
      intro x
      rw [standardFacetCarrierPrism_zero]
      exact (Classical.choose_spec
        (exists_standardFacetCarrierIntersectionPrism_zero d x)).symm
  | succ n ih =>
      intro x
      have hcycle := standardFacetCarrierPrismResidual_cycle_of_equation
        d (standardFacetCarrierPrism d) n ih x
      have hfill :=
        standardPuncturedFacetIntersectionIntegralTotalCycleFiller_boundary
          d n (standardFacetCarrier d x)
          (standardFacetCarrier_nonempty d x)
          (standardFacetCarrier_ne_univ d x)
          (standardFacetCarrierPrismResidual d
            (standardFacetCarrierPrism d) n x) hcycle
      rw [standardFacetCarrierPrism_succ, hfill, standardFacetCarrierPrismResidual]
      abel

/-- The degree-raising carrier-prism family, extended by zero away from adjacent degrees. -/
def standardFacetCarrierPrismHom (d i j : ℕ) :
    (CoverSmallIntegralSingularChainComplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).X i ⟶
    ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
      (AddCommGrpCat.of ℤ)).X j :=
  if h : j = i + 1 then by
    subst j
    exact standardFacetCarrierPrismComponent d
      (standardFacetCarrierPrism d) i
  else 0

@[simp]
lemma standardFacetCarrierPrismHom_succ (d i : ℕ) :
    standardFacetCarrierPrismHom d i (i + 1) =
      standardFacetCarrierPrismComponent d
        (standardFacetCarrierPrism d) i := by
  simp [standardFacetCarrierPrismHom]

/-- The ambient carrier discrepancy is integrally chain-homotopic to zero. -/
def standardFacetCarrierDiscrepancyIntegralHomotopy (d : ℕ) :
    Homotopy (standardFacetCarrierDiscrepancyChainMap d) 0 where
  hom := standardFacetCarrierPrismHom d
  zero i j hij := by
    rw [standardFacetCarrierPrismHom]
    split_ifs with h
    · exact absurd h.symm hij
    · rfl
  comm i := by
    cases i with
    | zero =>
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [standardFacetCarrierPrismHom_succ,
          HomologicalComplex.zero_f, add_zero, zero_add]
        exact standardFacetCarrierPrismComponent_boundary_zero d
          (standardFacetCarrierPrism d)
          (standardFacetCarrierPrism_equation d 0)
    | succ n =>
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex]
        simp only [standardFacetCarrierPrismHom_succ,
          HomologicalComplex.zero_f, add_zero]
        exact standardFacetCarrierPrismComponent_boundary_succ d
          (standardFacetCarrierPrism d) n
          (standardFacetCarrierPrism_equation d (n + 1))

/-- Rationalization of the acyclic-carrier homotopy. -/
def standardFacetCarrierDiscrepancyRationalHomotopy (d : ℕ) :
    Homotopy
      (rationalizeSimplicialChainMap
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
        (TopCat.toSSet.obj (standardPuncturedPair d).snd)
        (standardFacetCarrierDiscrepancyChainMap d)) 0 :=
  (rationalizeSimplicialChainHomotopy
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (TopCat.toSSet.obj (standardPuncturedPair d).snd)
    (standardFacetCarrierDiscrepancyIntegralHomotopy d)).trans
      (Homotopy.ofEq (rationalizeSimplicialChainMap_zero
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
        (TopCat.toSSet.obj (standardPuncturedPair d).snd)))

/-- The integral affine-boundary chain map. -/
def standardAffineBoundaryIntegralChainMap (d : ℕ) :
    ((∂Δ[d] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)) ⟶
      (TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap (standardAffineBoundarySimplicialMap d)
    (AddCommGrpCat.of ℤ)

/-- Barycentric subdivision followed by last vertex on the facet-small simplicial set. -/
def standardFacetSmallBarycentricLastVertexIntegralChainMap (d : ℕ) :
    CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
      CoverSmallIntegralSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) :=
  barycentricSubdivisionChainMapCanonical
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) ≫
    subdivisionLastVertexChainMap
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)

lemma standardFacetCarrierAffineIntersectionMap_comp_ambientInclusion
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    standardFacetCarrierAffineIntersectionMap d x ≫
        TopCat.toSSet.map
          (topologicalSubsetInclusion (standardPuncturedPair d).snd
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x))) =
      standardFacetCarrierBoundarySimplexMap d x ≫
        standardAffineBoundarySimplicialMap d := by
  unfold standardFacetCarrierAffineIntersectionMap
  exact singularSimplicialMapLiftToSubset_comp_inclusion _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma standardFacetCarrierSourceSubdivisionIntersectionMap_comp_ambientInclusion
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    standardFacetCarrierSourceSubdivisionIntersectionMap d x ≫
        TopCat.toSSet.map
          (topologicalSubsetInclusion (standardPuncturedPair d).snd
            (standardPuncturedFacetIntersectionSubspace d
              (standardFacetCarrier d x))) =
      simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫
        SSet.yonedaEquiv.symm x.1 := by
  unfold standardFacetCarrierSourceSubdivisionIntersectionMap
  have hsource : standardFacetCarrierSourceIntersectionMap d x ≫
      TopCat.toSSet.map
        (topologicalSubsetInclusion (standardPuncturedPair d).snd
          (standardPuncturedFacetIntersectionSubspace d
            (standardFacetCarrier d x))) =
      SSet.yonedaEquiv.symm x.1 := by
    unfold standardFacetCarrierSourceIntersectionMap
    exact singularSimplicialMapLiftToSubset_comp_inclusion _ _ _ _ _
  simpa only [Category.assoc] using congrArg
    (fun f ↦ simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫ f) hsource

set_option backward.isDefEq.respectTransparency false in
/-- Subdivision, last vertex, and the simplex represented by `x` give the same map whether
formed in the cover-small simplicial set or directly in the ambient singular set. -/
lemma standardFacetSmall_subdivision_to_source
    (d n : ℕ)
    (x : (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) _⦋n⦌) :
    SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk n) ≫
        SSet.sd.map (SSet.yonedaEquiv.symm x) ≫
        subdivisionLastVertex.app
          (coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) ≫
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).ι =
      simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫
        SSet.yonedaEquiv.symm x.1 := by
  let K : SSet.{0} := coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
  let inc : K ⟶ TopCat.toSSet.obj (standardPuncturedPair d).snd :=
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).ι
  have hy : SSet.yonedaEquiv.symm x ≫ inc = SSet.yonedaEquiv.symm x.1 :=
    SSet.yonedaEquiv_symm_comp x
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).ι
  have hnatInc : subdivisionLastVertex.app K ≫ inc =
      SSet.sd.map inc ≫ subdivisionLastVertex.app
        (TopCat.toSSet.obj (standardPuncturedPair d).snd) :=
    (subdivisionLastVertex.naturality inc).symm
  have hnatSimplex :
      SSet.sd.map (SSet.yonedaEquiv.symm x.1) ≫
          subdivisionLastVertex.app
            (TopCat.toSSet.obj (standardPuncturedPair d).snd) =
        subdivisionLastVertex.app (Δ[n] : SSet.{0}) ≫
          SSet.yonedaEquiv.symm x.1 :=
    subdivisionLastVertex.naturality (SSet.yonedaEquiv.symm x.1)
  let A := SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk n)
  let B := SSet.sd.map (SSet.yonedaEquiv.symm x)
  let L := subdivisionLastVertex.app K
  calc
    ((A ≫ B) ≫ L) ≫ inc = (A ≫ B) ≫ (L ≫ inc) :=
      Category.assoc _ _ _
    _ = (A ≫ B) ≫
        (SSet.sd.map inc ≫ subdivisionLastVertex.app
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)) := by rw [hnatInc]
    _ = A ≫ ((B ≫ SSet.sd.map inc) ≫
        subdivisionLastVertex.app
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)) := by
      simp only [Category.assoc]
    _ = A ≫ (SSet.sd.map (SSet.yonedaEquiv.symm x ≫ inc) ≫
        subdivisionLastVertex.app
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)) := by
      rw [SSet.sd.map_comp]
    _ = A ≫ (SSet.sd.map (SSet.yonedaEquiv.symm x.1) ≫
        subdivisionLastVertex.app
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)) := by rw [hy]
    _ = A ≫ (subdivisionLastVertex.app (Δ[n] : SSet.{0}) ≫
        SSet.yonedaEquiv.symm x.1) := by rw [hnatSimplex]
    _ = (A ≫ subdivisionLastVertex.app (Δ[n] : SSet.{0})) ≫
        SSet.yonedaEquiv.symm x.1 := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [subdivisionLastVertex_standardSimplex]

set_option backward.isDefEq.respectTransparency false in
lemma standardFacetCarrierDiscrepancyChainMap_eq (d : ℕ) :
    standardFacetCarrierDiscrepancyChainMap d =
      (standardFacetCarrierChainMap d ≫
          standardAffineBoundaryIntegralChainMap d :
        CoverSmallIntegralSingularChainComplex
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
          IntegralSingularChainComplexObj (standardPuncturedPair d).snd) -
        standardFacetSmallBarycentricLastVertexIntegralChainMap d ≫
          coverSmallIntegralSingularChainInclusion
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (coverSmallSingularSubcomplex
    (standardPuncturedPair d).snd
      (standardPuncturedFacetCover d) : SSet).chainComplex_hom_ext
  intro x
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f]
  rw [standardFacetCarrierDiscrepancyChainMap_f,
    iota_standardFacetCarrierDiscrepancyComponent,
    standardFacetCarrierDiscrepancySimplexChain,
    standardFacetCarrierIntersectionDiscrepancy,
    Preadditive.sub_comp, Preadditive.comp_sub]
  apply congrArg₂ (fun a b ↦ a - b)
  · rw [← Category.assoc, standardFacetCarrierChainMap_f,
      iota_standardFacetCarrierComponent, standardFacetCarrierSimplexChain]
    simp only [Category.assoc]
    have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).congr_map
      (standardFacetCarrierAffineIntersectionMap_comp_ambientInclusion d n x)
    rw [Functor.map_comp, Functor.map_comp] at hmap
    exact congrArg (fun k ↦ subdividedSimplexFundamentalChain n ≫ k.f n) hmap
  · rw [← Category.assoc, standardFacetSmallBarycentricLastVertexIntegralChainMap,
      HomologicalComplex.comp_f, barycentricSubdivisionChainMapCanonical_f, ← Category.assoc,
      iota_barycentricSubdivisionComponent, barycentricSubdivisionSimplexChain,
      subdividedStandardSimplexFundamentalChain]
    simp only [Category.assoc]
    let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
    have hleft := F.congr_map
      (standardFacetCarrierSourceSubdivisionIntersectionMap_comp_ambientInclusion d n x)
    have hright := F.congr_map
      (standardFacetSmall_subdivision_to_source d n x)
    rw [Functor.map_comp] at hleft
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at hright
    have htotal := hleft.trans hright.symm
    have hntotal := congrArg (fun k ↦ k.f n) htotal
    simp only [HomologicalComplex.comp_f] at hntotal
    unfold standardFacetCarrierIntersectionChainInclusion subdivisionLastVertexChainMap
      coverSmallIntegralSingularChainInclusion
    dsimp only [F] at hntotal
    simpa only [Category.assoc] using
      congrArg (fun k ↦ subdividedSimplexFundamentalChain n ≫ k) hntotal

lemma standardAffineBoundarySimplicialMap_range_le_coverSmall (d : ℕ) :
    SSet.Subcomplex.range (standardAffineBoundarySimplicialMap d) ≤
      coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) := by
  rintro q _ ⟨y, rfl⟩
  obtain ⟨i, hi⟩ := (SSet.mem_boundary_iff_notMem_range y.1).mp y.2
  rw [mem_coverSmallSingularSubcomplex_iff]
  exact ⟨i, (singularSimplex_mem_range_subset
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d i) _).mpr
    (standardAffineBoundarySimplex_image_subset_facetCover d q.unop.len y i hi)⟩

/-- The affine boundary simplicial map factored through cover-small singular simplices. -/
def standardAffineBoundaryToFacetSmall (d : ℕ) :
    (∂Δ[d] : SSet.{0}) ⟶
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet) :=
  SSet.Subcomplex.lift (standardAffineBoundarySimplicialMap d)
    (standardAffineBoundarySimplicialMap_range_le_coverSmall d)

@[reassoc (attr := simp)]
lemma standardAffineBoundaryToFacetSmall_comp_inclusion (d : ℕ) :
    standardAffineBoundaryToFacetSmall d ≫
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).ι =
      standardAffineBoundarySimplicialMap d :=
  SSet.Subcomplex.lift_ι _ _

lemma standardAffineBoundary_vertex_mem_facetCover_iff
    (d n : ℕ) (y : (∂Δ[d] : SSet.{0}) _⦋n⦌)
    (a : Fin (n + 1)) (i : Fin (d + 1)) :
    ((standardPuncturedPair d).snd.toSSetObjEquiv _
      ((standardAffineBoundarySimplicialMap d).app _ y))
        (stdSimplex.vertex a) ∈ standardPuncturedFacetCover d i ↔
      i ≠ y.1 a := by
  change (∃ j : Fin (d + 1),
    standardExtendedCoordinate d i
        (standardAffineSimplex d (stdSimplex.map y.1 (stdSimplex.vertex a))) <
      standardExtendedCoordinate d j
        (standardAffineSimplex d (stdSimplex.map y.1 (stdSimplex.vertex a)))) ↔ _
  rw [stdSimplex.map_vertex]
  simp only [standardExtendedCoordinate_standardAffineSimplex,
    sub_lt_sub_iff_right]
  constructor
  · rintro ⟨j, hj⟩ rfl
    have hle : (stdSimplex.vertex (y.1 a) :
        stdSimplex ℝ (Fin (d + 1))) j ≤ 1 :=
      stdSimplex.le_one _ j
    have hone : (stdSimplex.vertex (y.1 a) :
        stdSimplex ℝ (Fin (d + 1))) (y.1 a) = 1 := by simp
    rw [hone] at hj
    exact (not_lt_of_ge hle) hj
  · intro h
    refine ⟨y.1 a, ?_⟩
    simp [stdSimplex.vertex, h]

lemma standardAffineBoundarySmall_vertex_mem_facetCover_iff
    (d n : ℕ) (y : (∂Δ[d] : SSet.{0}) _⦋n⦌)
    (a : Fin (n + 1)) (i : Fin (d + 1)) :
    ((standardPuncturedPair d).snd.toSSetObjEquiv _
      ((standardAffineBoundaryToFacetSmall d).app _ y).1)
        (stdSimplex.vertex a) ∈ standardPuncturedFacetCover d i ↔
      i ≠ y.1 a :=
  standardAffineBoundary_vertex_mem_facetCover_iff d n y a i

/-- On an affine boundary simplex, the complementary carrier of a face is exactly the image of
that face's vertex set. -/
lemma standardFacetComplementCarrier_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetComplementCarrier d
        ((standardAffineBoundaryToFacetSmall d).app _ y) A =
      A.finset.image (fun a ↦ y.1 a.down) := by
  classical
  ext i
  simp only [standardFacetComplementCarrier, Finset.mem_compl,
    standardFacetCarrierAtFace, Finset.mem_filter, Finset.mem_univ, true_and,
    standardAffineBoundarySmall_vertex_mem_facetCover_iff,
    Finset.mem_image]
  constructor
  · intro h
    by_contra hnot
    exact h fun a ha hai ↦ hnot ⟨a, ha, hai.symm⟩
  · rintro ⟨a, ha, rfl⟩ h
    exact h a ha rfl

lemma standardFacetComplementCarrierMax_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    standardFacetComplementCarrierMax d
        ((standardAffineBoundaryToFacetSmall d).app _ y) A =
      y.1 (A.finset.max' A.nonempty).down := by
  classical
  unfold standardFacetComplementCarrierMax
  have hcarrier := standardFacetComplementCarrier_affine d n y A
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    rw [hcarrier, Finset.mem_image] at hj
    obtain ⟨a, ha, rfl⟩ := hj
    have haDown : a.down ≤ (A.finset.max' A.nonempty).down := Finset.le_max' A.finset a ha
    exact (SSet.stdSimplex.objEquiv y.1).toOrderHom.monotone haDown
  · apply Finset.le_max'
    rw [hcarrier]
    exact Finset.mem_image.mpr
      ⟨A.finset.max' A.nonempty, Finset.max'_mem _ _, rfl⟩

lemma standardFacetCarrierSimplexMap_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌) :
    standardFacetCarrierSimplexMap d
        ((standardAffineBoundaryToFacetSmall d).app _ y) =
      simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫
        SSet.yonedaEquiv.symm y.1 := by
  ext q F
  rcases q with ⟨⟨k⟩⟩
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  let A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) := F.obj r
  change standardFacetComplementCarrierMax d
      ((standardAffineBoundaryToFacetSmall d).app _ y) A =
    y.1 (nonemptyFiniteChainMaximum
      (ULift.{0} (Fin (n + 1))) A).down
  rw [nonemptyFiniteChainMaximum_apply]
  exact standardFacetComplementCarrierMax_affine d n y A

lemma standardFacetCarrierBoundarySimplexMap_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌) :
    standardFacetCarrierBoundarySimplexMap d
        ((standardAffineBoundaryToFacetSmall d).app _ y) =
      simplexSubdivisionLastVertex.app (SimplexCategory.mk n) ≫
        SSet.yonedaEquiv.symm y := by
  apply (cancel_mono (∂Δ[d]).ι).mp
  rw [standardFacetCarrierBoundarySimplexMap_comp_inclusion,
    standardFacetCarrierSimplexMap_affine, Category.assoc]
  have hy : SSet.yonedaEquiv.symm y ≫ (∂Δ[d]).ι =
      SSet.yonedaEquiv.symm y.1 :=
    SSet.yonedaEquiv_symm_comp y (∂Δ[d]).ι
  rw [hy]

lemma standardSubdivisionToCarrierBoundary_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌) :
    SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk n) ≫
        SSet.sd.map (SSet.yonedaEquiv.symm y) ≫
        subdivisionLastVertex.app (∂Δ[d] : SSet.{0}) =
      standardFacetCarrierBoundarySimplexMap d
        ((standardAffineBoundaryToFacetSmall d).app _ y) := by
  rw [standardFacetCarrierBoundarySimplexMap_affine, subdivisionLastVertex.naturality,
    ← Category.assoc, subdivisionLastVertex_standardSimplex]
  rfl

/-- On each affine simplex, carrier after subdivision is the usual subdivision--last-vertex
endomorphism of the simplicial boundary. -/
lemma standardFacetCarrierSimplexChain_affine (d n : ℕ)
    (y : (∂Δ[d] : SSet.{0}) _⦋n⦌) :
    standardFacetCarrierSimplexChain d n
        ((standardAffineBoundaryToFacetSmall d).app _ y) =
      (∂Δ[d] : SSet.{0}).ιChainComplex y ≫
        (barycentricSubdivisionChainMapCanonical (∂Δ[d] : SSet.{0}) ≫
          subdivisionLastVertexChainMap (∂Δ[d] : SSet.{0})).f n := by
  rw [standardFacetCarrierSimplexChain]
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, barycentricSubdivisionChainMapCanonical_f,
    iota_barycentricSubdivisionComponent, barycentricSubdivisionSimplexChain,
    subdividedStandardSimplexFundamentalChain]
  simp only [Category.assoc]
  congr 1
  have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).congr_map
    (standardSubdivisionToCarrierBoundary_affine d n y)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun f ↦ f.f n) hmap.symm

lemma standardAffineSmall_comp_standardFacetCarrierChainMap (d : ℕ) :
    SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d)
        (AddCommGrpCat.of ℤ) ≫
      standardFacetCarrierChainMap d =
    barycentricSubdivisionChainMapCanonical (∂Δ[d] : SSet.{0}) ≫
      subdivisionLastVertexChainMap (∂Δ[d] : SSet.{0}) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply (∂Δ[d] : SSet.{0}).chainComplex_hom_ext
  intro y
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, standardFacetCarrierChainMap_f,
    iota_standardFacetCarrierComponent]
  exact standardFacetCarrierSimplexChain_affine d n y

/-- The rationalized carrier chain map. -/
def standardFacetCarrierRationalChainMap (d : ℕ) :
    CoverSmallRationalSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)) :=
  rationalizeSimplicialChainMap
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (∂Δ[d] : SSet.{0}) (standardFacetCarrierChainMap d)

/-- The rational subdivision--last-vertex endomorphism. -/
def standardBarycentricLastVertexRationalChainMap (d : ℕ) :
    ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)) ⟶
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)) :=
  rationalizeSimplicialChainMap (∂Δ[d] : SSet.{0}) (∂Δ[d] : SSet.{0})
    (barycentricSubdivisionChainMapCanonical (∂Δ[d] : SSet.{0}) ≫
      subdivisionLastVertexChainMap (∂Δ[d] : SSet.{0}))

/-- The rational subdivision--last-vertex endomorphism is chain-homotopic to the identity. -/
def standardBarycentricLastVertexRationalHomotopy (d : ℕ) :
    Homotopy (standardBarycentricLastVertexRationalChainMap d) (𝟙 _) :=
  (rationalizeSimplicialChainHomotopy (∂Δ[d] : SSet.{0}) (∂Δ[d] : SSet.{0})
    (barycentricSubdivisionLastVertexHomotopyCanonical (∂Δ[d] : SSet.{0}))).trans
      (Homotopy.ofEq (rationalizeSimplicialChainMap_id (∂Δ[d] : SSet.{0})))

lemma standardAffineSmallRational_comp_standardFacetCarrierRationalChainMap (d : ℕ) :
    SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d)
        (ModuleCat.of ℚ ℚ) ≫
      standardFacetCarrierRationalChainMap d =
    standardBarycentricLastVertexRationalChainMap d := by
  rw [← rationalizeSimplicialChainMap_chainComplexMap]
  unfold standardFacetCarrierRationalChainMap
  rw [← rationalizeSimplicialChainMap_comp, standardAffineSmall_comp_standardFacetCarrierChainMap]
  rfl

lemma standardAffineBoundaryChainMap_factor_facetSmall (d : ℕ) :
    SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d)
        (ModuleCat.of ℚ ℚ) ≫
      coverSmallRationalSingularChainInclusion
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) =
    standardAffineBoundaryChainMap d := by
  change SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d)
      (ModuleCat.of ℚ ℚ) ≫
    SSet.chainComplexMap
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d)).ι
      (ModuleCat.of ℚ ℚ) =
    SSet.chainComplexMap (standardAffineBoundarySimplicialMap d)
      (ModuleCat.of ℚ ℚ)
  rw [← Functor.map_comp, standardAffineBoundaryToFacetSmall_comp_inclusion]

/-- Rationalization preserves subtraction of integral simplicial chain maps. -/
lemma rationalizeSimplicialChainMap_sub
    (X Y : SSet.{0})
    (f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    rationalizeSimplicialChainMap X Y (f - g) =
      rationalizeSimplicialChainMap X Y f -
        rationalizeSimplicialChainMap X Y g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [rationalizeSimplicialChainMap_f,
    sub_eq_add_neg,
    rationalizeSimplicialChainComponent_add,
    rationalizeSimplicialChainComponent_neg,
    HomologicalComplex.add_f_apply, HomologicalComplex.neg_f_apply]

/-- Rational subdivision followed by last vertex on the facet-small simplicial set. -/
def standardFacetSmallBarycentricLastVertexRationalChainMap (d : ℕ) :
    CoverSmallRationalSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) ⟶
      CoverSmallRationalSingularChainComplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) :=
  rationalizeSimplicialChainMap
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (standardFacetSmallBarycentricLastVertexIntegralChainMap d)

/-- The rationalized carrier discrepancy is the difference between carrier followed by affine
realization and subdivision--last-vertex followed by small-chain inclusion. -/
lemma standardFacetCarrierDiscrepancyRationalChainMap_eq (d : ℕ) :
    rationalizeSimplicialChainMap
        (coverSmallSingularSubcomplex
          (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
        (TopCat.toSSet.obj (standardPuncturedPair d).snd)
        (standardFacetCarrierDiscrepancyChainMap d) =
      standardFacetCarrierRationalChainMap d ≫
          standardAffineBoundaryChainMap d -
        standardFacetSmallBarycentricLastVertexRationalChainMap d ≫
          coverSmallRationalSingularChainInclusion
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) := by
  rw [standardFacetCarrierDiscrepancyChainMap_eq]
  calc
    _ = rationalizeSimplicialChainMap
          (coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)
          (standardFacetCarrierChainMap d ≫
            standardAffineBoundaryIntegralChainMap d) -
        rationalizeSimplicialChainMap
          (coverSmallSingularSubcomplex
            (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
          (TopCat.toSSet.obj (standardPuncturedPair d).snd)
          (standardFacetSmallBarycentricLastVertexIntegralChainMap d ≫
            coverSmallIntegralSingularChainInclusion
              (standardPuncturedPair d).snd
              (standardPuncturedFacetCover d)) :=
      rationalizeSimplicialChainMap_sub _ _ _ _
    _ = _ := by
      apply congrArg₂ (fun f g ↦ f - g)
      · rw [rationalizeSimplicialChainMap_comp]
        unfold standardFacetCarrierRationalChainMap standardAffineBoundaryIntegralChainMap
          standardAffineBoundaryChainMap
        rw [rationalizeSimplicialChainMap_chainComplexMap]
      · unfold coverSmallIntegralSingularChainInclusion
        rw [rationalizeSimplicialChainMap_comp]
        unfold standardFacetSmallBarycentricLastVertexRationalChainMap
          coverSmallRationalSingularChainInclusion
        rw [rationalizeSimplicialChainMap_chainComplexMap]

/-- On facet-small rational chains, subdivision followed by last vertex is homotopic to the
identity. -/
def standardFacetSmallBarycentricLastVertexRationalHomotopy (d : ℕ) :
    Homotopy (standardFacetSmallBarycentricLastVertexRationalChainMap d) ( 𝟙 _) :=
  (rationalizeSimplicialChainHomotopy
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (coverSmallSingularSubcomplex
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)
    (barycentricSubdivisionLastVertexHomotopyCanonical
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet))).trans
    (Homotopy.ofEq (rationalizeSimplicialChainMap_id
      (coverSmallSingularSubcomplex
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d) : SSet)))

/-- The rational carrier followed by affine realization is homotopic to the inclusion of
facet-small rational chains. -/
def standardFacetCarrierAffineRationalHomotopy (d : ℕ) :
    Homotopy
      (standardFacetCarrierRationalChainMap d ≫
        standardAffineBoundaryChainMap d)
      (coverSmallRationalSingularChainInclusion
        (standardPuncturedPair d).snd (standardPuncturedFacetCover d)) := by
  let C := standardFacetCarrierRationalChainMap d ≫
    standardAffineBoundaryChainMap d
  let B := standardFacetSmallBarycentricLastVertexRationalChainMap d
  let I := coverSmallRationalSingularChainInclusion
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
  have hnull : Homotopy (C - B ≫ I) 0 :=
    (Homotopy.ofEq
      (standardFacetCarrierDiscrepancyRationalChainMap_eq d).symm).trans
        (standardFacetCarrierDiscrepancyRationalHomotopy d)
  exact ((Homotopy.equivSubZero (f := C) (g := B ≫ I)).symm hnull).trans
    ((standardFacetSmallBarycentricLastVertexRationalHomotopy d).compRightId I)

/-- A chain-level left inverse of affine realization, obtained by smallifying with respect to
the facet cover and then applying the explicit carrier map. -/
def standardAffineBoundaryChainRetraction (d : ℕ) :
    ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
      (ModuleCat.of ℚ ℚ)) ⟶
    ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)) :=
  (coverSmallRationalChainHomotopyEquiv_of_openCover
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
      (isOpen_standardPuncturedFacetCover d)
      (iUnion_standardPuncturedFacetCover d)).inv ≫
    standardFacetCarrierRationalChainMap d

/-- Affine realization followed by the explicit carrier retraction is chain-homotopic to the
identity. -/
def standardAffineBoundaryChainRetractionHomotopy (d : ℕ) :
    Homotopy
      (standardAffineBoundaryChainMap d ≫
        standardAffineBoundaryChainRetraction d)
      (𝟙 ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ))) := by
  let A := SSet.chainComplexMap (standardAffineBoundaryToFacetSmall d)
    (ModuleCat.of ℚ ℚ)
  let E := coverSmallRationalChainHomotopyEquiv_of_openCover
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
    (isOpen_standardPuncturedFacetCover d)
    (iUnion_standardPuncturedFacetCover d)
  let C := standardFacetCarrierRationalChainMap d
  have hfac : standardAffineBoundaryChainMap d = A ≫ E.hom := by
    rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom]
    exact (standardAffineBoundaryChainMap_factor_facetSmall d).symm
  have hstart : standardAffineBoundaryChainMap d ≫ (E.inv ≫ C) =
      (A ≫ (E.hom ≫ E.inv)) ≫ C := by
    rw [hfac]
    simp only [Category.assoc]
  have hsmall : Homotopy ((A ≫ (E.hom ≫ E.inv)) ≫ C)
      ((A ≫ 𝟙 _) ≫ C) :=
    (E.homotopyHomInvId.compLeft A).compRight C
  have hunit : (A ≫ 𝟙 _) ≫ C = A ≫ C := by simp
  have hcarrier : A ≫ C = standardBarycentricLastVertexRationalChainMap d :=
    standardAffineSmallRational_comp_standardFacetCarrierRationalChainMap d
  exact (Homotopy.ofEq hstart).trans <| hsmall.trans <|
    (Homotopy.ofEq hunit).trans <| (Homotopy.ofEq hcarrier).trans <|
      standardBarycentricLastVertexRationalHomotopy d

/-- The explicit carrier retraction followed by affine realization is chain-homotopic to the
identity on punctured-space rational chains. -/
def standardAffineBoundaryChainCoretractionHomotopy (d : ℕ) :
    Homotopy
      (standardAffineBoundaryChainRetraction d ≫
        standardAffineBoundaryChainMap d)
      (𝟙 ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (ModuleCat.of ℚ ℚ))) := by
  let E := coverSmallRationalChainHomotopyEquiv_of_openCover
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
    (isOpen_standardPuncturedFacetCover d)
    (iUnion_standardPuncturedFacetCover d)
  let C := standardFacetCarrierRationalChainMap d
  let A := standardAffineBoundaryChainMap d
  let I := coverSmallRationalSingularChainInclusion
    (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
  have hE : E.hom = I :=
    coverSmallRationalChainHomotopyEquiv_of_openCover_hom
      (standardPuncturedPair d).snd (standardPuncturedFacetCover d)
      (isOpen_standardPuncturedFacetCover d)
      (iUnion_standardPuncturedFacetCover d)
  have hcarrier : Homotopy (C ≫ A) E.hom :=
    (standardFacetCarrierAffineRationalHomotopy d).trans
      (Homotopy.ofEq hE.symm)
  have hfull : Homotopy (E.inv ≫ (C ≫ A)) (𝟙 _) :=
    (hcarrier.compLeft E.inv).trans E.homotopyInvHomId
  simpa only [standardAffineBoundaryChainRetraction, Category.assoc] using hfull

/-- Affine realization of the standard simplicial boundary is a rational chain-homotopy
equivalence onto punctured Euclidean space. -/
def standardAffineBoundaryChainHomotopyEquiv (d : ℕ) :
    HomotopyEquiv
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ))
      ((TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (ModuleCat.of ℚ ℚ)) where
  hom := standardAffineBoundaryChainMap d
  inv := standardAffineBoundaryChainRetraction d
  homotopyHomInvId := standardAffineBoundaryChainRetractionHomotopy d
  homotopyInvHomId := standardAffineBoundaryChainCoretractionHomotopy d

/-- The map on rational homology induced by the affine realization of a standard simplicial
sphere in punctured Euclidean space. -/
def standardAffineBoundaryHomologyMap (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) ⟶
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) :=
  HomologicalComplex.homologyMap
    (standardAffineBoundaryChainMap (n + 2)) (n + 1)

/-- The induced map on homology back to the simplicial boundary. -/
def standardAffineBoundaryHomologyRetraction (n : ℕ) :
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) ⟶
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) :=
  HomologicalComplex.homologyMap
    (standardAffineBoundaryChainRetraction (n + 2)) (n + 1)

lemma standardAffineBoundaryHomologyMap_comp_retraction (n : ℕ) :
    standardAffineBoundaryHomologyMap n ≫
        standardAffineBoundaryHomologyRetraction n = 𝟙 _ := by
  rw [standardAffineBoundaryHomologyMap,
    standardAffineBoundaryHomologyRetraction,
    ← HomologicalComplex.homologyMap_comp,
    (standardAffineBoundaryChainRetractionHomotopy (n + 2)).homologyMap_eq,
    HomologicalComplex.homologyMap_id]

/-- The homology isomorphism induced by affine realization of the standard simplicial
boundary. -/
def standardAffineBoundaryHomologyIso (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) ≅
    ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) :=
  (standardAffineBoundaryChainHomotopyEquiv (n + 2)).toHomologyIso (n + 1)

@[simp]
lemma standardAffineBoundaryHomologyIso_hom (n : ℕ) :
    (standardAffineBoundaryHomologyIso n).hom =
      standardAffineBoundaryHomologyMap n :=
  rfl

/-- The affine boundary comparison is an isomorphism on rational homology. -/
noncomputable instance standardAffineBoundaryHomologyMap_isIso (n : ℕ) :
    IsIso (standardAffineBoundaryHomologyMap n) := by
  change IsIso (HomologicalComplex.homologyMap
    (standardAffineBoundaryChainHomotopyEquiv (n + 2)).hom (n + 1))
  exact ((standardAffineBoundaryChainHomotopyEquiv (n + 2)).toHomologyIso
    (n + 1)).isIso_hom

lemma standardAffineBoundaryHomologyMap_injective (n : ℕ) :
    Function.Injective (standardAffineBoundaryHomologyMap n).hom := by
  intro x y hxy
  have h := congrArg (standardAffineBoundaryHomologyRetraction n).hom hxy
  have hcomp := ConcreteCategory.congr_hom
    (standardAffineBoundaryHomologyMap_comp_retraction n)
  calc
    x = (standardAffineBoundaryHomologyRetraction n).hom
        ((standardAffineBoundaryHomologyMap n).hom x) := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
        using (hcomp x).symm
    _ = (standardAffineBoundaryHomologyRetraction n).hom
        ((standardAffineBoundaryHomologyMap n).hom y) := h
    _ = y := by
      simpa only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply]
        using hcomp y

lemma standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain' (n : ℕ) :
    standardSphereSimplicialBoundaryChain n ≫
        (standardAffineBoundaryChainMap (n + 1)).f n =
      standardSubspaceBoundaryChain n := by
  rw [standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain,
    standardPuncturedAffineBoundaryChain, standardSubspaceBoundaryChain]

lemma standardPuncturedBoundaryCycle_inclusion' (n : ℕ) :
    standardPuncturedBoundaryCycle n ≫
        ((chainPairFunctor ℚ).obj
          (standardPuncturedPair (n + 1))).left.iCycles n =
      standardSubspaceBoundaryChain n := by
  rw [standardPuncturedBoundaryCycle, HomologicalComplex.liftCycles_i]

lemma standardPuncturedBoundaryCycle_direct_inclusion (n : ℕ) :
    standardPuncturedBoundaryCycle n ≫
        ((TopCat.toSSet.obj (standardPuncturedPair (n + 1)).snd).chainComplex
          (ModuleCat.of ℚ ℚ)).iCycles n =
      standardSubspaceBoundaryChain n :=
  standardPuncturedBoundaryCycle_inclusion' n

lemma standardSphereSimplicialBoundaryCycle_inclusion' (n : ℕ) :
    standardSphereSimplicialBoundaryCycle n ≫
        ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of ℚ ℚ)).iCycles (n + 1) =
      standardSphereSimplicialBoundaryChain (n + 1) := by
  rw [standardSphereSimplicialBoundaryCycle,
    HomologicalComplex.liftCycles_i]

set_option backward.isDefEq.respectTransparency false in
/-- The affine image of the simplicial alternating-facet cycle is the punctured Euclidean
alternating-facet cycle. -/
lemma standardSphereSimplicialBoundaryCycle_affine (n : ℕ) :
    standardSphereSimplicialBoundaryCycle n ≫
        HomologicalComplex.cyclesMap
          (standardAffineBoundaryChainMap (n + 2)) (n + 1) =
      standardPuncturedBoundaryCycle (n + 1) := by
  have hcycles :
      HomologicalComplex.cyclesMap
          (standardAffineBoundaryChainMap (n + 2)) (n + 1) ≫
        ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
          (ModuleCat.of ℚ ℚ)).iCycles (n + 1) =
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of ℚ ℚ)).iCycles (n + 1) ≫
        (standardAffineBoundaryChainMap (n + 2)).f (n + 1) :=
    HomologicalComplex.cyclesMap_i (standardAffineBoundaryChainMap (n + 2)) (n + 1)
  apply (cancel_mono
    (((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
      (ModuleCat.of ℚ ℚ)).iCycles (n + 1))).mp
  rw [Category.assoc, hcycles, standardPuncturedBoundaryCycle_direct_inclusion,
    ← Category.assoc, standardSphereSimplicialBoundaryCycle_inclusion']
  exact standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain'
    (n + 1)

set_option backward.isDefEq.respectTransparency false in
/-- On homology, the affine realization sends the known simplicial sphere generator to the
explicit boundary class in punctured Euclidean space. -/
lemma standardAffineBoundaryHomologyMap_standardSphereSimplicialBoundaryClass (n : ℕ) :
    (standardAffineBoundaryHomologyMap n).hom
        (standardSphereSimplicialBoundaryClass n) =
      standardPuncturedBoundaryClass (n + 1) := by
  have hmor :
      standardSphereSimplicialBoundaryCycle n ≫
          ((∂Δ[n + 2] : SSet.{0}).chainComplex
            (ModuleCat.of ℚ ℚ)).homologyπ (n + 1) ≫
          standardAffineBoundaryHomologyMap n =
        standardPuncturedBoundaryCycle (n + 1) ≫
          ((TopCat.toSSet.obj (standardPuncturedPair (n + 2)).snd).chainComplex
            (ModuleCat.of ℚ ℚ)).homologyπ (n + 1) := by
    change standardSphereSimplicialBoundaryCycle n ≫
        ((∂Δ[n + 2] : SSet.{0}).chainComplex
          (ModuleCat.of ℚ ℚ)).homologyπ (n + 1) ≫
        HomologicalComplex.homologyMap
          (standardAffineBoundaryChainMap (n + 2)) (n + 1) = _
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      standardSphereSimplicialBoundaryCycle_affine]
  exact ConcreteCategory.congr_hom hmor 1

/-- Injectivity of the explicit affine boundary comparison implies nonvanishing of the
punctured Euclidean boundary class. -/
lemma standardPuncturedBoundaryClass_succ_ne_zero_of_affine_injective
    (n : ℕ) (h : Function.Injective (standardAffineBoundaryHomologyMap n).hom) :
    standardPuncturedBoundaryClass (n + 1) ≠ 0 := by
  intro hz
  apply standardSphereSimplicialBoundaryClass_ne_zero n
  apply h
  rw [standardAffineBoundaryHomologyMap_standardSphereSimplicialBoundaryClass,
    hz, map_zero]
  rfl

/-- The explicit oriented boundary class is nonzero in every degree. -/
lemma standardPuncturedBoundaryClass_succ_ne_zero (n : ℕ) :
    standardPuncturedBoundaryClass (n + 1) ≠ 0 :=
  standardPuncturedBoundaryClass_succ_ne_zero_of_affine_injective n
    (standardAffineBoundaryHomologyMap_injective n)

/-- If the affine boundary comparison is an isomorphism, its explicit punctured class spans
top homology. -/
lemma span_standardPuncturedBoundaryClass_succ_eq_top_of_affine_isIso
    (n : ℕ) [IsIso (standardAffineBoundaryHomologyMap n)] :
    Submodule.span ℚ {standardPuncturedBoundaryClass (n + 1)} = ⊤ := by
  let e := (asIso (standardAffineBoundaryHomologyMap n)).toLinearEquiv
  have he : e (standardSphereSimplicialBoundaryClass n) =
      standardPuncturedBoundaryClass (n + 1) :=
    standardAffineBoundaryHomologyMap_standardSphereSimplicialBoundaryClass n
  have hmap :
      (Submodule.span ℚ {standardSphereSimplicialBoundaryClass n}).map e.toLinearMap =
        Submodule.span ℚ {standardPuncturedBoundaryClass (n + 1)} := by
    rw [Submodule.map_span]
    simp [he]
    rfl
  have etop : (⊤ : Submodule ℚ _).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  rw [← hmap, span_standardSphereSimplicialBoundaryClass_eq_top, etop]
  rfl

/-- The explicit standard local class is nonzero in every positive dimension. -/
lemma standardLocalClass_ne_zero_of_pos (d : ℕ) (hd : 0 < d) :
    standardLocalClass d ≠ 0 := by
  cases d with
  | zero => lia
  | succ n =>
      cases n with
      | zero => exact standardLocalClass_one_ne_zero
      | succ n =>
          rw [standardLocalClass_succ_ne_zero_iff (n + 1) (by lia)]
          exact standardPuncturedBoundaryClass_succ_ne_zero n

/-- In dimensions at least two, an affine-boundary homology isomorphism makes the standard
relative local class a generator. -/
lemma span_standardLocalClass_add_two_eq_top_of_affine_isIso
    (n : ℕ) [IsIso (standardAffineBoundaryHomologyMap n)] :
    Submodule.span ℚ {standardLocalClass (n + 2)} = ⊤ := by
  rw [span_standardLocalClass_succ_eq_top_iff (n + 1) (by lia)]
  exact span_standardPuncturedBoundaryClass_succ_eq_top_of_affine_isIso n

/-- In every dimension at least two, the explicit standard relative local class generates
rational local homology. -/
lemma span_standardLocalClass_add_two_eq_top (n : ℕ) :
    Submodule.span ℚ {standardLocalClass (n + 2)} = ⊤ :=
  span_standardLocalClass_add_two_eq_top_of_affine_isIso n

end AlgebraicTopology.Singular
