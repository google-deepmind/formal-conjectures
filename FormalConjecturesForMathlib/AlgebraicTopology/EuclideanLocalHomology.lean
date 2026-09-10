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

public import FormalConjecturesForMathlib.AlgebraicTopology.LocalFundamentalClass
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.Equiv

import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

/-!
# Euclidean local homology

This file develops the long exact sequence of the standard punctured Euclidean pair and computes
the connecting morphism on the explicit standard local class. These are the chain-level
prerequisites for proving that the standard class generates local homology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits ContinuousMap
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- The short complex of subspace, ambient, and relative rational singular chains. -/
def relativeSingularChainShortComplex (X : TopPair) :
    ShortComplex (ChainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk ((chainPairFunctor ℚ).obj X).hom
    (relativeChainProjection ℚ X)
    (subspaceChainMap_relativeChainProjection ℚ X)

/-- Singular chains turn the subspace inclusion of a topological pair into a monomorphism. -/
lemma relativeSingularChainMap_mono (X : TopPair) :
    Mono ((chainPairFunctor ℚ).obj X).hom := by
  let : Mono X.hom :=
    (TopCat.mono_iff_injective X.hom).mpr X.prop.injective
  change Mono (((singularChainComplexFunctor (ModuleCat ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map X.hom)
  apply Functor.map_mono

/-- The subspace, ambient, and relative rational singular chain complexes form a short exact
sequence. -/
lemma relativeSingularChainShortComplex_shortExact (X : TopPair) :
    (relativeSingularChainShortComplex X).ShortExact := by
  let : Mono ((chainPairFunctor ℚ).obj X).hom := relativeSingularChainMap_mono X
  exact
    { exact := ShortComplex.exact_cokernel ((chainPairFunctor ℚ).obj X).hom
      mono_f := by
        dsimp [relativeSingularChainShortComplex]
        infer_instance
      epi_g := by
        dsimp [relativeSingularChainShortComplex, relativeChainProjection]
        constructor
        intro Z g h w
        exact Cofork.IsColimit.hom_ext
          (cokernelIsCokernel ((chainPairFunctor ℚ).obj X).hom) w }

/-- The connecting map from relative homology in degree `n + 1` to subspace homology in degree
`n`. -/
def relativeSingularBoundary (X : TopPair) (n : ℕ) :
    RelativeHomology ℚ X (n + 1) ⟶ Homology ℚ X.snd n :=
  (relativeSingularChainShortComplex_shortExact X).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by lia))

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at ambient homology in the long exact sequence of a topological pair. -/
lemma relativeSingular_homology_exact_ambient (X : TopPair) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n)
      (HomologicalComplex.homologyMap (relativeChainProjection ℚ X) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp]
        change HomologicalComplex.homologyMap
          (((chainPairFunctor ℚ).obj X).hom ≫
            cokernel.π ((chainPairFunctor ℚ).obj X).hom) n = 0
        rw [cokernel.condition, HomologicalComplex.homologyMap_zero])).Exact :=
  (relativeSingularChainShortComplex_shortExact X).homology_exact₂ n

/-- Exactness at relative homology in the long exact sequence of a topological pair. -/
lemma relativeSingular_homology_exact_relative (X : TopPair) (n : ℕ) :
    (ShortComplex.mk
      (relativeHomologyProjection ℚ X (n + 1))
      (relativeSingularBoundary X n)
      (by
        exact (relativeSingularChainShortComplex_shortExact X).comp_δ
          (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia)))).Exact :=
  (relativeSingularChainShortComplex_shortExact X).homology_exact₃
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))

/-- Exactness at subspace homology in the long exact sequence of a topological pair. -/
lemma relativeSingular_homology_exact_subspace (X : TopPair) (n : ℕ) :
    (ShortComplex.mk
      (relativeSingularBoundary X n)
      (HomologicalComplex.homologyMap ((chainPairFunctor ℚ).obj X).hom n)
      (by
        exact (relativeSingularChainShortComplex_shortExact X).δ_comp
          (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia)))).Exact :=
  (relativeSingularChainShortComplex_shortExact X).homology_exact₁
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))

/-- The alternating sum of the faces of the standard affine `(n + 1)`-simplex, regarded as a
chain in punctured Euclidean space. -/
def standardSubspaceBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val • standardSubspaceFaceChain n i

lemma standardSubspaceBoundaryChain_inclusion (n : ℕ) :
    standardSubspaceBoundaryChain n ≫
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).hom.f n =
    standardAmbientSimplexChain (n + 1) ≫
      ((chainPairFunctor ℚ).obj
        (standardPuncturedPair (n + 1))).right.d (n + 1) n := by
  rw [standardSubspaceBoundaryChain, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, standardFaceChain_inclusion]
  exact (standardAmbientSimplexChain_boundary n).symm

lemma standardSubspaceBoundaryChain_boundary (n : ℕ) :
    standardSubspaceBoundaryChain n ≫
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.d n
        ((ComplexShape.down ℕ).next n) = 0 := by
  let f := ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).hom
  let : Mono f := relativeSingularChainMap_mono (standardPuncturedPair (n + 1))
  let : Mono (f.f ((ComplexShape.down ℕ).next n)) :=
    Functor.map_mono (HomologicalComplex.eval (ModuleCat ℚ) _
      ((ComplexShape.down ℕ).next n)) f
  rw [← cancel_mono (f.f ((ComplexShape.down ℕ).next n)), Category.assoc, ← f.comm,
    ← Category.assoc, standardSubspaceBoundaryChain_inclusion, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]
  simp

/-- The boundary of the standard affine simplex as a cycle in punctured Euclidean space. -/
def standardPuncturedBoundaryCycle (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.cycles n :=
  ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.liftCycles
    (standardSubspaceBoundaryChain n) ((ComplexShape.down ℕ).next n) rfl
    (standardSubspaceBoundaryChain_boundary n)

/-- The homology class of the boundary of the standard affine simplex in punctured Euclidean
space. -/
def standardPuncturedBoundaryClass (n : ℕ) :
    Homology ℚ (standardPuncturedPair (n + 1)).snd n :=
  ((standardPuncturedBoundaryCycle n ≫
    ((chainPairFunctor ℚ).obj
      (standardPuncturedPair (n + 1))).left.homologyπ n).hom) 1

lemma standardLocalCycle_comp_relativeSingularBoundary (n : ℕ) :
    standardLocalCycle (n + 1) ≫
        (standardLocalRelativeChainComplex (n + 1)).homologyπ (n + 1) ≫
        relativeSingularBoundary (standardPuncturedPair (n + 1)) n =
      standardPuncturedBoundaryCycle n ≫
        ((chainPairFunctor ℚ).obj
          (standardPuncturedPair (n + 1))).left.homologyπ n := by
  let S := relativeSingularChainShortComplex (standardPuncturedPair (n + 1))
  let hS := relativeSingularChainShortComplex_shortExact
    (standardPuncturedPair (n + 1))
  exact hS.δ_eq (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))
    (standardLocalChain (n + 1)) (standardLocalChain_boundary_succ n)
    (standardAmbientSimplexChain (n + 1)) rfl
    (standardSubspaceBoundaryChain n) (standardSubspaceBoundaryChain_inclusion n)
    ((ComplexShape.down ℕ).next n) rfl

/-- The connecting map sends the standard local class to the homology class of the oriented
boundary of the standard affine simplex. -/
lemma relativeSingularBoundary_standardLocalClass (n : ℕ) :
    (relativeSingularBoundary (standardPuncturedPair (n + 1)) n).hom
        (standardLocalClass (n + 1)) =
      standardPuncturedBoundaryClass n :=
  ConcreteCategory.congr_hom (standardLocalCycle_comp_relativeSingularBoundary n) 1

/-! ### Contractibility of the ambient Euclidean space -/

/-- A specified homotopy equivalence induces an isomorphism on rational singular homology. -/
def rationalSingularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (k : ℕ) (e : X ≃ₕ Y) :
    Homology ℚ (TopCat.of X) k ≅ Homology ℚ (TopCat.of Y) k := by
  let F := (singularHomologyFunctor (ModuleCat ℚ) k).obj (ModuleCat.of ℚ ℚ)
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  exact CategoryTheory.Iso.mk (F.map f) (F.map g) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.left_inv.some (ModuleCat.of ℚ ℚ) k) (by
    rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      e.right_inv.some (ModuleCat.of ℚ ℚ) k)

/-- Positive-degree rational singular homology of a real coordinate space vanishes. -/
lemma standardRealModel_homology_isZero (d k : ℕ) (hk : k ≠ 0) :
    IsZero (Homology ℚ (TopCat.of (StandardRealModel d)) k) := by
  let e := (ContractibleSpace.hequiv_unit (StandardRealModel d)).some
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat (R := ℚ)) k (ModuleCat.of ℚ ℚ) (TopCat.of Unit) hk).of_iso
      (rationalSingularHomologyIsoOfHomotopyEquiv k e)

/-- In positive degree, the connecting map identifies the local homology of Euclidean space with
the preceding homology of its punctured complement. -/
def standardPuncturedRelativeBoundaryIso (n : ℕ) (hn : n ≠ 0) :
    RelativeHomology ℚ (standardPuncturedPair (n + 1)) (n + 1) ≅
      Homology ℚ (standardPuncturedPair (n + 1)).snd n :=
  (relativeSingularChainShortComplex_shortExact (standardPuncturedPair (n + 1))).δIso
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))
    (standardRealModel_homology_isZero (n + 1) (n + 1) (by lia))
    (standardRealModel_homology_isZero (n + 1) n hn)

lemma standardPuncturedRelativeBoundaryIso_hom (n : ℕ) (hn : n ≠ 0) :
    (standardPuncturedRelativeBoundaryIso n hn).hom =
      relativeSingularBoundary (standardPuncturedPair (n + 1)) n := rfl

/-- Above dimension one, nonvanishing of the standard local class is equivalent to nonvanishing
of its explicit oriented boundary in the punctured Euclidean space. -/
lemma standardLocalClass_succ_ne_zero_iff (n : ℕ) (hn : n ≠ 0) :
    standardLocalClass (n + 1) ≠ 0 ↔ standardPuncturedBoundaryClass n ≠ 0 := by
  rw [← relativeSingularBoundary_standardLocalClass n,
    ← standardPuncturedRelativeBoundaryIso_hom n hn]
  exact (standardPuncturedRelativeBoundaryIso n hn).toLinearEquiv.map_ne_zero_iff.symm

/-- Above dimension one, the standard local class spans exactly when its explicit oriented
boundary spans the preceding homology of the punctured Euclidean space. -/
lemma span_standardLocalClass_succ_eq_top_iff (n : ℕ) (hn : n ≠ 0) :
    Submodule.span ℚ {standardLocalClass (n + 1)} = ⊤ ↔
      Submodule.span ℚ {standardPuncturedBoundaryClass n} = ⊤ := by
  let e := (standardPuncturedRelativeBoundaryIso n hn).toLinearEquiv
  have he : e (standardLocalClass (n + 1)) = standardPuncturedBoundaryClass n := by
    change (standardPuncturedRelativeBoundaryIso n hn).hom.hom
      (standardLocalClass (n + 1)) = _
    rw [standardPuncturedRelativeBoundaryIso_hom,
      relativeSingularBoundary_standardLocalClass]
  have hmap :
      (Submodule.span ℚ {standardLocalClass (n + 1)}).map e.toLinearMap =
        Submodule.span ℚ {standardPuncturedBoundaryClass n} := by
    rw [Submodule.map_span]
    simp [he]
  have etop : (⊤ : Submodule ℚ _).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  constructor
  · intro h
    rw [← hmap, h, etop]
  · intro h
    apply Submodule.map_injective_of_injective e.injective
    rw [hmap, h, etop]

/-! ### The standard class in dimension one -/

/-- The punctured real line, in the coordinates used by the standard local class. -/
abbrev StandardPuncturedLine := ({0}ᶜ : Set (StandardRealModel 1))

/-- The point `-1` of the standard punctured real line. -/
def standardNegativePoint : StandardPuncturedLine := ⟨fun _ ↦ -1, by
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have := congr_fun h 0
  norm_num at this⟩

/-- The point `1` of the standard punctured real line. -/
def standardPositivePoint : StandardPuncturedLine := ⟨fun _ ↦ 1, by
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have := congr_fun h 0
  norm_num at this⟩

/-- The negative and positive points lie in different path components of the punctured line. -/
lemma standardPuncturedLine_components_ne :
    ZerothHomotopy.mk standardNegativePoint ≠
      ZerothHomotopy.mk standardPositivePoint := by
  intro h
  have hj : Joined standardNegativePoint standardPositivePoint := Quotient.exact h
  obtain ⟨p⟩ := hj
  let g : unitInterval → ℝ := fun t ↦ (p t : StandardRealModel 1) 0
  have hg : Continuous g :=
    (((continuous_apply (0 : Fin 1)).comp continuous_subtype_val).comp p.continuous)
  have hg0 : g 0 = -1 := by
    change (p 0 : StandardRealModel 1) 0 = -1
    rw [show p 0 = standardNegativePoint from p.source]
    rfl
  have hg1 : g 1 = 1 := by
    change (p 1 : StandardRealModel 1) 0 = 1
    rw [show p 1 = standardPositivePoint from p.target]
    rfl
  have hz : (0 : ℝ) ∈ Set.range g :=
    intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hg (by
      rw [hg0, hg1]
      norm_num)
  obtain ⟨t, ht⟩ := hz
  apply (p t).property
  ext j
  fin_cases j
  exact ht

lemma standardFaceSimplex_zero_point :
    TopCat.toSSetObj₀Equiv (standardFaceSimplex 0 (0 : Fin 2)) =
      standardNegativePoint := by
  change standardFaceMap 0 (0 : Fin 2)
    (default : stdSimplex ℝ (Fin 1)) = standardNegativePoint
  rw [Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]
  apply Subtype.ext
  funext j
  fin_cases j
  simp [standardFaceMap, standardAffineSimplex, stdSimplex.map, standardNegativePoint]

lemma standardFaceSimplex_one_point :
    TopCat.toSSetObj₀Equiv (standardFaceSimplex 0 (1 : Fin 2)) =
      standardPositivePoint := by
  change standardFaceMap 0 (1 : Fin 2)
    (default : stdSimplex ℝ (Fin 1)) = standardPositivePoint
  rw [Subsingleton.elim (default : stdSimplex ℝ (Fin 1)) (stdSimplex.vertex 0)]
  apply Subtype.ext
  funext j
  fin_cases j
  simp [standardFaceMap, standardAffineSimplex, stdSimplex.map, standardPositivePoint]

/-- The two vertices of the standard one-simplex represent different components of the
punctured line. -/
lemma standardFaceSimplex_components_ne :
    SSet.π₀.mk (standardFaceSimplex 0 (0 : Fin 2)) ≠
      SSet.π₀.mk (standardFaceSimplex 0 (1 : Fin 2)) := by
  intro h
  have hz := congrArg
    (TopCat.zerothHomotopyEquiv (X := (standardPuncturedPair 1).snd)).symm h
  simp only [TopCat.zerothHomotopyEquiv_symm_mk] at hz
  rw [standardFaceSimplex_zero_point, standardFaceSimplex_one_point] at hz
  exact standardPuncturedLine_components_ne hz

/-- A vertex of the standard one-simplex, regarded as a zero-cycle in the punctured line. -/
def standardPuncturedFaceCycle (i : Fin 2) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.cycles 0 :=
  ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.liftCycles
    (standardSubspaceFaceChain 0 i) 0 (by simp) (by simp)

lemma standardPuncturedBoundaryCycle_zero_eq :
    standardPuncturedBoundaryCycle 0 =
      standardPuncturedFaceCycle 0 - standardPuncturedFaceCycle 1 := by
  rw [← cancel_mono
    (((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.iCycles 0)]
  rw [Preadditive.sub_comp]
  simp only [standardPuncturedBoundaryCycle, standardPuncturedFaceCycle,
    HomologicalComplex.liftCycles_i]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • standardSubspaceFaceChain 0 i) =
    standardSubspaceFaceChain 0 0 - standardSubspaceFaceChain 0 1
  rw [Fin.sum_univ_two]
  norm_num
  rw [sub_eq_add_neg]

set_option backward.isDefEq.respectTransparency false in
lemma standardPuncturedFaceCycle_homology₀Iso (i : Fin 2) :
    standardPuncturedFaceCycle i ≫
        ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.homologyπ 0 ≫
        ((TopCat.toSSet.obj (standardPuncturedPair 1).snd).homology₀Iso
          (ModuleCat.of ℚ ℚ)).hom =
      Sigma.ι (fun (_ : (TopCat.toSSet.obj (standardPuncturedPair 1).snd).π₀) ↦
        ModuleCat.of ℚ ℚ) (SSet.π₀.mk (standardFaceSimplex 0 i)) :=
  SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
    (TopCat.toSSet.obj (standardPuncturedPair 1).snd) (ModuleCat.of ℚ ℚ)
      (standardFaceSimplex 0 i)

set_option backward.isDefEq.respectTransparency false in
lemma standardPuncturedBoundaryCycle_homology₀Iso :
    standardPuncturedBoundaryCycle 0 ≫
        ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.homologyπ 0 ≫
        ((TopCat.toSSet.obj (standardPuncturedPair 1).snd).homology₀Iso
          (ModuleCat.of ℚ ℚ)).hom =
      Sigma.ι (fun (_ : (TopCat.toSSet.obj (standardPuncturedPair 1).snd).π₀) ↦
          ModuleCat.of ℚ ℚ) (SSet.π₀.mk (standardFaceSimplex 0 0)) -
        Sigma.ι (fun (_ : (TopCat.toSSet.obj (standardPuncturedPair 1).snd).π₀) ↦
          ModuleCat.of ℚ ℚ) (SSet.π₀.mk (standardFaceSimplex 0 1)) := by
  rw [standardPuncturedBoundaryCycle_zero_eq, Preadditive.sub_comp,
    standardPuncturedFaceCycle_homology₀Iso, standardPuncturedFaceCycle_homology₀Iso]

/-- A linear functional detecting the negative component of the punctured line. -/
def standardPuncturedBoundaryDetector :
    (∐ (fun (_ : (TopCat.toSSet.obj (standardPuncturedPair 1).snd).π₀) ↦
      ModuleCat.of ℚ ℚ)) ⟶ ModuleCat.of ℚ ℚ := by
  classical
  exact Sigma.desc fun j ↦
    if j = SSet.π₀.mk (standardFaceSimplex 0 0) then 𝟙 _ else 0

set_option backward.isDefEq.respectTransparency false in
lemma standardPuncturedBoundaryCycle_detect :
    standardPuncturedBoundaryCycle 0 ≫
        ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.homologyπ 0 ≫
        ((TopCat.toSSet.obj (standardPuncturedPair 1).snd).homology₀Iso
          (ModuleCat.of ℚ ℚ)).hom ≫ standardPuncturedBoundaryDetector = 𝟙 _ := by
  calc
    _ = (standardPuncturedBoundaryCycle 0 ≫
          ((chainPairFunctor ℚ).obj (standardPuncturedPair 1)).left.homologyπ 0 ≫
          ((TopCat.toSSet.obj (standardPuncturedPair 1).snd).homology₀Iso
            (ModuleCat.of ℚ ℚ)).hom) ≫ standardPuncturedBoundaryDetector := by
            simp only [Category.assoc]
    _ = _ := by
      rw [standardPuncturedBoundaryCycle_homology₀Iso, Preadditive.sub_comp]
      simp [standardPuncturedBoundaryDetector, Ne.symm standardFaceSimplex_components_ne]

set_option backward.isDefEq.respectTransparency false in
/-- The oriented boundary of the standard one-simplex is nonzero in the zero-dimensional
homology of the punctured line. -/
lemma standardPuncturedBoundaryClass_zero_ne_zero :
    standardPuncturedBoundaryClass 0 ≠ 0 := by
  intro h
  have hdet := ConcreteCategory.congr_hom standardPuncturedBoundaryCycle_detect 1
  change (standardPuncturedBoundaryDetector.hom
      (((TopCat.toSSet.obj (standardPuncturedPair 1).snd).homology₀Iso
        (ModuleCat.of ℚ ℚ)).hom.hom (standardPuncturedBoundaryClass 0))) = 1 at hdet
  rw [h] at hdet
  norm_num at hdet

/-- The explicit standard local class is nonzero in
`H₁(ℝ, ℝ ∖ {0}; ℚ)`. -/
lemma standardLocalClass_one_ne_zero : standardLocalClass 1 ≠ 0 := by
  intro h
  apply standardPuncturedBoundaryClass_zero_ne_zero
  rw [← relativeSingularBoundary_standardLocalClass 0, h, map_zero]

end AlgebraicTopology.Singular
