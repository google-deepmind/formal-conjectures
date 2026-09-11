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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionMesh

import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionRelativeMesh

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Support of iterated affine subdivision

This file connects the permutation expansion of affine barycentric subdivision with the
geometric ancestry cells used in the mesh estimate.  It then lifts an iterate whose ancestry
cells are subordinate to a cover into the cover-small singular chain complex.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set Simplicial

namespace AlgebraicTopology.Singular

/-- The singular simplex obtained by restricting `x` to one iterated affine ancestry cell. -/
public noncomputable def iteratedAffineCellSingularSimplex
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (TopAffineFlag n)) :
    (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  (X.toSSetObjEquiv _).symm
    ((X.toSSetObjEquiv _ x).comp (iteratedAffineCellMap n ancestry))

@[simp]
public theorem toSSetObjEquiv_iteratedAffineCellSingularSimplex_apply
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (TopAffineFlag n))
    (w : stdSimplex ℝ (Fin (n + 1))) :
    X.toSSetObjEquiv _
        (iteratedAffineCellSingularSimplex X n x ancestry) w =
      X.toSSetObjEquiv _ x (iteratedAffineCellMap n ancestry w) := by
  rfl

@[simp]
public theorem iteratedAffineCellSingularSimplex_nil
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    iteratedAffineCellSingularSimplex X n x [] = x := by
  apply (X.toSSetObjEquiv _).injective
  rfl

/-- Adding the newest flag to an ancestry is the same as restricting the parent cell by that
affine flag. -/
public theorem iteratedAffineCellSingularSimplex_cons
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : TopAffineFlag n) (ancestry : List (TopAffineFlag n)) :
    iteratedAffineCellSingularSimplex X n x (F :: ancestry) =
      (TopCat.toSSet.map
        (singularSimplexTopCatMap X n
          (iteratedAffineCellSingularSimplex X n x ancestry))).app _
        (affineFlagSingularSimplex n n F) := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro w
  rfl

/-- Restricting a parent ancestry cell by one more flag adds that flag at the head of the
ancestry. -/
public theorem iteratedAffineCellSingularSimplex_singleton_parent
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (F : TopAffineFlag n) (ancestry : List (TopAffineFlag n)) :
    iteratedAffineCellSingularSimplex X n
        (iteratedAffineCellSingularSimplex X n x ancestry) [F] =
      iteratedAffineCellSingularSimplex X n x (F :: ancestry) := by
  calc
    iteratedAffineCellSingularSimplex X n
        (iteratedAffineCellSingularSimplex X n x ancestry) [F] =
        (TopCat.toSSet.map
          (singularSimplexTopCatMap X n
            (iteratedAffineCellSingularSimplex X n x ancestry))).app _
          (affineFlagSingularSimplex n n F) := by
            rw [iteratedAffineCellSingularSimplex_cons,
              iteratedAffineCellSingularSimplex_nil]
    _ = iteratedAffineCellSingularSimplex X n x (F :: ancestry) :=
      (iteratedAffineCellSingularSimplex_cons X n x F ancestry).symm

/-- One affine subdivision of a generator is exactly the signed sum over permutation maximal
flags. -/
public theorem affineSubdivisionSingularSimplexChain_eq_permutation_sum
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    affineSubdivisionSingularSimplexChain X n x =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        permutationSignInteger σ •
          (TopCat.toSSet.obj X).ιChainComplex
            (iteratedAffineCellSingularSimplex X n x
              [permutationMaximalFlagSimplex σ]) := by
  rw [affineSubdivisionSingularSimplexChain,
    affineSubdividedSimplexFundamentalChain,
    subdividedSimplexFundamentalChain, Preadditive.sum_comp,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Preadditive.zsmul_comp,
    affineFlagChainMap_f, iota_affineFlagChainComponent,
    SSet.ι_chainComplexMap_f]
  apply congrArg (fun f ↦ permutationSignInteger σ • f)
  rw [iteratedAffineCellSingularSimplex_cons,
    iteratedAffineCellSingularSimplex_nil]

/-- A depth-`m` choice of one permutation maximal flag at every subdivision stage. -/
public abbrev AffinePermutationAncestry (n m : ℕ) :=
  Fin m → Equiv.Perm (Fin (n + 1))

/-- The list of affine flags encoded by a permutation ancestry, newest first. -/
public noncomputable def affinePermutationAncestryFlags
    (n m : ℕ) (a : AffinePermutationAncestry n m) :
    List (TopAffineFlag n) :=
  List.ofFn fun i ↦ permutationMaximalFlagSimplex (a i)

/-- The product of the orientation signs along a permutation ancestry. -/
public noncomputable def affinePermutationAncestrySign
    (n m : ℕ) (a : AffinePermutationAncestry n m) : ℤ :=
  ∏ i, permutationSignInteger (a i)

@[simp]
public theorem affinePermutationAncestryFlags_zero
    (n : ℕ) (a : AffinePermutationAncestry n 0) :
    affinePermutationAncestryFlags n 0 a = [] := by
  simp [affinePermutationAncestryFlags]

@[simp]
public theorem affinePermutationAncestrySign_zero
    (n : ℕ) (a : AffinePermutationAncestry n 0) :
    affinePermutationAncestrySign n 0 a = 1 := by
  simp [affinePermutationAncestrySign]

@[simp]
public theorem affinePermutationAncestryFlags_cons
    (n m : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (a : AffinePermutationAncestry n m) :
    affinePermutationAncestryFlags n (m + 1) (Fin.cons σ a) =
      permutationMaximalFlagSimplex σ ::
        affinePermutationAncestryFlags n m a := by
  simp [affinePermutationAncestryFlags]

@[simp]
public theorem affinePermutationAncestrySign_cons
    (n m : ℕ) (σ : Equiv.Perm (Fin (n + 1)))
    (a : AffinePermutationAncestry n m) :
    affinePermutationAncestrySign n (m + 1) (Fin.cons σ a) =
      permutationSignInteger σ * affinePermutationAncestrySign n m a := by
  simp [affinePermutationAncestrySign, Fin.prod_univ_succ]

/-- The exact generator expansion after `m` affine subdivisions.  Its summands are precisely the
singular simplices obtained from depth-`m` affine ancestries. -/
public theorem iota_affineSingularSubdivisionIterate_eq_ancestry_sum
    (X : TopCat.{0}) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∀ m : ℕ,
      (TopCat.toSSet.obj X).ιChainComplex x ≫
          (affineSingularSubdivisionIterate X m).f n =
        ∑ a : AffinePermutationAncestry n m,
          affinePermutationAncestrySign n m a •
            (TopCat.toSSet.obj X).ιChainComplex
              (iteratedAffineCellSingularSimplex X n x
                (affinePermutationAncestryFlags n m a)) := by
  intro m
  induction m with
  | zero =>
      classical
      simp only [affineSingularSubdivisionIterate_zero]
      rw [Fintype.sum_unique]
      simp
  | succ m ih =>
      classical
      rw [affineSingularSubdivisionIterate_succ]
      change ((TopCat.toSSet.obj X).ιChainComplex x ≫
          (affineSingularSubdivisionIterate X m).f n) ≫
            (affineSingularSubdivisionChainMap X).f n = _
      rw [ih, Preadditive.sum_comp]
      simp only [Preadditive.zsmul_comp,
        affineSingularSubdivisionChainMap_f,
        iota_affineSingularSubdivisionComponent,
        affineSubdivisionSingularSimplexChain_eq_permutation_sum,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm, ← Fintype.sum_prod_type']
      apply Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (m + 1) ↦
          Equiv.Perm (Fin (n + 1)))) _ _
      rintro ⟨σ, a⟩
      change (affinePermutationAncestrySign n m a *
          permutationSignInteger σ) • _ =
        affinePermutationAncestrySign n (m + 1) (Fin.cons σ a) •
          (TopCat.toSSet.obj X).ιChainComplex
            (iteratedAffineCellSingularSimplex X n x
              (affinePermutationAncestryFlags n (m + 1) (Fin.cons σ a)))
      rw [affinePermutationAncestrySign_cons,
        affinePermutationAncestryFlags_cons, mul_comm,
        iteratedAffineCellSingularSimplex_singleton_parent]

section CoverSmall

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- A geometric ancestry cell subordinate to one cover member defines a cover-small singular
simplex. -/
public theorem iteratedAffineCellSingularSimplex_mem_coverSmall
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (iteratedAffineCellMap n ancestry) ⊆ U i) :
    iteratedAffineCellSingularSimplex X n x ancestry ∈
      (coverSmallSingularSubcomplex X U).obj
        (Opposite.op (SimplexCategory.mk n)) := by
  rw [mem_coverSmallSingularSubcomplex_iff_exists_preimage]
  obtain ⟨i, hi⟩ := hsmall
  let f : C(stdSimplex ℝ (Fin (n + 1)), U i) :=
    ⟨fun w ↦
      ⟨X.toSSetObjEquiv _ x (iteratedAffineCellMap n ancestry w),
        hi ⟨iteratedAffineCellMap n ancestry w, ⟨w, rfl⟩, rfl⟩⟩,
      Continuous.subtype_mk
        ((X.toSSetObjEquiv _ x).continuous.comp
          (iteratedAffineCellMap n ancestry).continuous) _⟩
  refine ⟨i, (TopCat.toSSetObjEquiv _ _).symm f, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro w
  rfl

/-- The cover-small simplex corresponding to a subordinate ancestry cell. -/
public noncomputable def coverSmallIteratedAffineCellSimplex
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (iteratedAffineCellMap n ancestry) ⊆ U i) :
    (coverSmallSingularSubcomplex X U : SSet).obj
      (Opposite.op (SimplexCategory.mk n)) :=
  ⟨iteratedAffineCellSingularSimplex X n x ancestry,
    iteratedAffineCellSingularSimplex_mem_coverSmall X U n x ancestry hsmall⟩

@[simp]
public theorem coverSmallIteratedAffineCellSimplex_val
    (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (ancestry : List (TopAffineFlag n))
    (hsmall : ∃ i, X.toSSetObjEquiv _ x ''
      Set.range (iteratedAffineCellMap n ancestry) ⊆ U i) :
    (coverSmallIteratedAffineCellSimplex X U n x ancestry hsmall).1 =
      iteratedAffineCellSingularSimplex X n x ancestry :=
  rfl

/-- The signed ancestry expansion, lifted generator by generator to cover-small chains. -/
public noncomputable def coverSmallAffineAncestryLiftChain
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    AddCommGrpCat.of ℤ ⟶
      (CoverSmallIntegralSingularChainComplex X U).X n :=
  ∑ a : AffinePermutationAncestry n m,
    affinePermutationAncestrySign n m a •
      (coverSmallSingularSubcomplex X U : SSet).ιChainComplex
        (coverSmallIteratedAffineCellSimplex X U n x
          (affinePermutationAncestryFlags n m a) (hsmall a))

/-- The lifted ancestry chain maps to the actual affine-subdivision iterate of its original
generator. -/
public theorem coverSmallAffineAncestryLiftChain_comp_inclusion
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    coverSmallAffineAncestryLiftChain X U n m x hsmall ≫
        (coverSmallIntegralSingularChainInclusion X U).f n =
      (TopCat.toSSet.obj X).ιChainComplex x ≫
        (affineSingularSubdivisionIterate X m).f n := by
  change coverSmallAffineAncestryLiftChain X U n m x hsmall ≫
      (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)).f n = _
  rw [coverSmallAffineAncestryLiftChain, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  exact (iota_affineSingularSubdivisionIterate_eq_ancestry_sum X n x m).symm

/-- If every depth-`m` ancestry cell of a generator is subordinate to the cover, its subdivided
chain lies in the degreewise range of the cover-small inclusion. -/
public theorem affineSingularSubdivisionIterate_generator_mem_range_of_ancestries
    (n m : ℕ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))
    (hsmall : ∀ a : AffinePermutationAncestry n m,
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (iteratedAffineCellMap n
          (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    (affineSingularSubdivisionIterate X m).f n
        ((TopCat.toSSet.obj X).ιChainComplex
          (R := AddCommGrpCat.of ℤ) x 1) ∈
      Set.range ((coverSmallIntegralSingularChainInclusion X U).f n) := by
  refine ⟨coverSmallAffineAncestryLiftChain X U n m x hsmall 1, ?_⟩
  exact ConcreteCategory.congr_hom
    (coverSmallAffineAncestryLiftChain_comp_inclusion X U n m x hsmall) 1

@[simp]
public theorem length_affinePermutationAncestryFlags
    (n m : ℕ) (a : AffinePermutationAncestry n m) :
    (affinePermutationAncestryFlags n m a).length = m := by
  simp [affinePermutationAncestryFlags]

/-- Once an iterate lies in the range of the cover-small inclusion, every later iterate does as
well. -/
public theorem affineSingularSubdivisionIterate_mem_range_add
    (n m r : ℕ)
    (c : (IntegralSingularChainComplexObj X).X n)
    (h : (affineSingularSubdivisionIterate X m).f n c ∈
      Set.range ((coverSmallIntegralSingularChainInclusion X U).f n)) :
    (affineSingularSubdivisionIterate X (m + r)).f n c ∈
      Set.range ((coverSmallIntegralSingularChainInclusion X U).f n) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨(coverSmallAffineSubdivisionIterate X U r).f n y, ?_⟩
  have hcomm := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.f n)
      (coverSmallAffineSubdivisionIterate_comp_inclusion X U r)) y
  have hmiddle :
      (affineSingularSubdivisionIterate X r).f n
          ((coverSmallIntegralSingularChainInclusion X U).f n y) =
        (affineSingularSubdivisionIterate X r).f n
          ((affineSingularSubdivisionIterate X m).f n c) :=
    congrArg ((affineSingularSubdivisionIterate X r).f n) hy
  have htotal :
      (affineSingularSubdivisionIterate X r).f n
          ((affineSingularSubdivisionIterate X m).f n c) =
        (affineSingularSubdivisionIterate X (m + r)).f n c := by
    rw [affineSingularSubdivisionIterate_add]
    rfl
  exact hcomm.trans (hmiddle.trans htotal)

/-- Chains which become cover-small after some (chain-dependent) number of affine subdivisions
form an additive subgroup. -/
public noncomputable def affineSubdivisionEventuallySmallAddSubgroup
    (n : ℕ) : AddSubgroup ((IntegralSingularChainComplexObj X).X n) where
  carrier := {c | ∃ m : ℕ,
    (affineSingularSubdivisionIterate X m).f n c ∈
      Set.range ((coverSmallIntegralSingularChainInclusion X U).f n)}
  zero_mem' :=
    ⟨0, 0, ((coverSmallIntegralSingularChainInclusion X U).f n).hom.map_zero.trans
      ((affineSingularSubdivisionIterate X 0).f n).hom.map_zero.symm⟩
  add_mem' := by
    rintro c d ⟨m, hm⟩ ⟨r, hr⟩
    have hm' := affineSingularSubdivisionIterate_mem_range_add
      X U n m r c hm
    have hr' := affineSingularSubdivisionIterate_mem_range_add
      X U n r m d hr
    rw [Nat.add_comm r m] at hr'
    obtain ⟨yc, hyc⟩ := hm'
    obtain ⟨yd, hyd⟩ := hr'
    refine ⟨m + r, yc + yd, ?_⟩
    simp only [map_add]
    rw [hyc, hyd]
    exact ((affineSingularSubdivisionIterate X (m + r)).f n).hom.map_add c d |>.symm
  neg_mem' := by
    rintro c ⟨m, hm⟩
    obtain ⟨y, hy⟩ := hm
    refine ⟨m, -y, ?_⟩
    simp only [map_neg]
    rw [hy]
    exact ((affineSingularSubdivisionIterate X m).f n).hom.map_neg c |>.symm

/-- Generatorwise subordinate permutation ancestries suffice for every chain: the required
subdivision depth may depend on the chain. -/
public theorem exists_affineSubdivisionIterate_mem_range_of_generator_ancestries
    (n : ℕ)
    (hsmall : ∀ x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n)),
      ∃ m : ℕ, ∀ a : AffinePermutationAncestry n m,
        ∃ i, X.toSSetObjEquiv _ x ''
          Set.range (iteratedAffineCellMap n
            (affinePermutationAncestryFlags n m a)) ⊆ U i) :
    ∀ c : (IntegralSingularChainComplexObj X).X n,
      ∃ m : ℕ, (affineSingularSubdivisionIterate X m).f n c ∈
        Set.range ((coverSmallIntegralSingularChainInclusion X U).f n) := by
  let P := affineSubdivisionEventuallySmallAddSubgroup X U n
  let Q := AddCommGrpCat.of ((IntegralSingularChainComplexObj X).X n ⧸ P)
  let q : (IntegralSingularChainComplexObj X).X n ⟶ Q :=
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' P)
  have hq : q = 0 := by
    apply (TopCat.toSSet.obj X).chainComplex_hom_ext
    intro x
    let j : AddCommGrpCat.of ℤ ⟶ (IntegralSingularChainComplexObj X).X n :=
      (TopCat.toSSet.obj X).ιChainComplex x
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change QuotientAddGroup.mk' P (j z) = 0
    obtain ⟨m, hm⟩ := hsmall x
    have hgen : j 1 ∈ P :=
      ⟨m, affineSingularSubdivisionIterate_generator_mem_range_of_ancestries
        X U n m x hm⟩
    have hzsmul := P.zsmul_mem hgen z
    have heq : j z = z • j 1 := by
      calc
        j z = j (z • (1 : ℤ)) := by simp
        _ = z • j 1 := j.hom.map_zsmul z 1
    rw [← heq] at hzsmul
    show j z ∈ (QuotientAddGroup.mk' P).ker
    rwa [QuotientAddGroup.ker_mk']
  intro c
  have hc : QuotientAddGroup.mk' P c = 0 := ConcreteCategory.congr_hom hq c
  change c ∈ P
  have hcker : c ∈ (QuotientAddGroup.mk' P).ker := hc
  rwa [QuotientAddGroup.ker_mk'] at hcker

/-- If all ancestry cells of one common depth are subordinate for each singular simplex, then
every chain in that degree has a cover-small subdivision iterate. -/
public theorem exists_affineSubdivisionIterate_mem_range_of_ancestries
    (n : ℕ)
    (hsmall : ∀ x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n)),
      ∃ m : ℕ, ∀ ancestry : List (TopAffineFlag n),
        ancestry.length = m →
          ∃ i, X.toSSetObjEquiv _ x ''
            Set.range (iteratedAffineCellMap n ancestry) ⊆ U i) :
    ∀ c : (IntegralSingularChainComplexObj X).X n,
      ∃ m : ℕ, (affineSingularSubdivisionIterate X m).f n c ∈
        Set.range ((coverSmallIntegralSingularChainInclusion X U).f n) := by
  apply exists_affineSubdivisionIterate_mem_range_of_generator_ancestries X U n
  intro x
  obtain ⟨m, hm⟩ := hsmall x
  exact ⟨m, fun a ↦ hm (affinePermutationAncestryFlags n m a)
    (length_affinePermutationAncestryFlags n m a)⟩

/-- Cover-subordination of every depth-`m` ancestry cell (with a depth depending on the original
simplex and degree) implies affine eventual smallness for all singular chains. -/
public theorem coverSmallAffineSubdivisionEventuallySmall_of_ancestries
    (hsmall : ∀ (n : ℕ) (x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n))),
      ∃ m : ℕ, ∀ ancestry : List (TopAffineFlag n),
        ancestry.length = m →
          ∃ i, X.toSSetObjEquiv _ x ''
            Set.range (iteratedAffineCellMap n ancestry) ⊆ U i) :
    ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (CoverSmallIntegralSingularChainComplex X U).X n),
        (coverSmallIntegralSingularChainInclusion X U).f n y =
          (affineSingularSubdivisionIterate X m).f n x := by
  apply coverSmallAffineSubdivisionEventuallySmall_of_iterate_mem_range X U
  intro n c
  exact exists_affineSubdivisionIterate_mem_range_of_ancestries
    X U n (hsmall n) c

set_option linter.unnecessarySimpa false in
/-- Zero-dimensional singular simplices are already subordinate to any covering family. -/
public theorem exists_zero_dimensional_ancestry_depth_subordinate
    (hUcover : ⋃ i, U i = Set.univ)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    ∃ m : ℕ, ∀ ancestry : List (TopAffineFlag 0),
      ancestry.length = m →
        ∃ i, X.toSSetObjEquiv _ x ''
          Set.range (iteratedAffineCellMap 0 ancestry) ⊆ U i := by
  refine ⟨0, fun ancestry hlength ↦ ?_⟩
  cases ancestry with
  | cons F ancestry => simp at hlength
  | nil =>
  let w₀ : stdSimplex ℝ (Fin (0 + 1)) := Classical.arbitrary _
  have hwcover : X.toSSetObjEquiv _ x w₀ ∈ ⋃ i, U i := by
    rw [hUcover]
    trivial
  simp only [Set.mem_iUnion] at hwcover
  obtain ⟨i, hi⟩ := hwcover
  refine ⟨i, ?_⟩
  rintro y ⟨z, ⟨w, rfl⟩, rfl⟩
  have hw : w = w₀ := by
    apply Subtype.ext
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have hwone : w 0 = 1 := by simpa using w.property.2
    have hw₀one : w₀ 0 = 1 := by simpa using w₀.property.2
    exact hwone.trans hw₀one.symm
  simpa [hw] using hi

/-- Every finite singular chain becomes subordinate to an open cover after enough genuine affine
barycentric subdivisions: the proved relative mesh contraction handles the positive degrees, and
degree zero is already small. -/
public theorem coverSmallAffineSubdivisionEventuallySmall_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (CoverSmallIntegralSingularChainComplex X U).X n),
        (coverSmallIntegralSingularChainInclusion X U).f n y =
          (affineSingularSubdivisionIterate X m).f n x := by
  apply coverSmallAffineSubdivisionEventuallySmall_of_ancestries X U
  intro n x
  cases n with
  | zero =>
      exact exists_zero_dimensional_ancestry_depth_subordinate X U hUcover x
  | succ n =>
      exact exists_iteratedAffineCell_depth_subordinate X U hUopen hUcover
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x

end CoverSmall

end AlgebraicTopology.Singular
