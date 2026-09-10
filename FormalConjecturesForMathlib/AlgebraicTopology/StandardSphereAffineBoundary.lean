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
public import FormalConjecturesForMathlib.AlgebraicTopology.StandardSphereSimplicialHomology

import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The affine boundary map into punctured Euclidean space

The universal affine simplex meets the origin only at its barycenter. Restricting it to the
simplicial boundary therefore gives a simplicial map into punctured Euclidean space. This file
constructs that map in every dimension.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial Opposite
open scoped Simplicial

namespace AlgebraicTopology.Singular

lemma stdSimplex_map_apply_eq_zero_of_notMem_range
    {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (w : stdSimplex ℝ X) (y : Y)
    (hy : y ∉ Set.range f) :
    stdSimplex.map f w y = 0 := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact (hy ⟨x, (Finset.mem_filter.mp hx).2⟩).elim

/-- A simplex in the simplicial boundary, realized affinely in punctured coordinate space. -/
def standardAffineBoundarySimplex (d k : ℕ)
    (x : (∂Δ[d] : SSet.{0}).obj (op (SimplexCategory.mk k))) :
    C(stdSimplex ℝ (Fin (k + 1)), ({0}ᶜ : Set (StandardRealModel d))) where
  toFun t := ⟨standardAffineSimplex d (stdSimplex.map x.1 t), by
    obtain ⟨j, hj⟩ := (SSet.mem_boundary_iff_notMem_range x.1).mp x.2
    exact standardAffineSimplex_ne_zero_of_coord_zero d _ j
      (stdSimplex_map_apply_eq_zero_of_notMem_range x.1 t j hj)⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_standardAffineSimplex d).comp (stdSimplex.continuous_map x.1)) _

/-- The boundary of the universal affine `d`-simplex as a map of simplicial sets into the
singular simplicial set of punctured `ℝ^d`. -/
def standardAffineBoundarySimplicialMap (d : ℕ) :
    (∂Δ[d] : SSet.{0}) ⟶ TopCat.toSSet.obj (standardPuncturedPair d).snd where
  app n := ↾ fun x ↦ ((standardPuncturedPair d).snd.toSSetObjEquiv _).symm
    (standardAffineBoundarySimplex d n.unop.len x)
  naturality n m f := by
    ext x
    change ((standardPuncturedPair d).snd.toSSetObjEquiv m).symm
        (standardAffineBoundarySimplex d m.unop.len
          ((∂Δ[d] : SSet.{0}).map f x)) = _
    calc
      _ = ((standardPuncturedPair d).snd.toSSetObjEquiv m).symm
          ((standardAffineBoundarySimplex d n.unop.len x).comp
            ⟨stdSimplex.map f.unop, stdSimplex.continuous_map f.unop⟩) := by
        congr 1
        ext t
        simp only [standardAffineBoundarySimplex, ContinuousMap.coe_mk,
          ContinuousMap.comp_apply]
        rw [stdSimplex.map_comp_apply]
        rfl
      _ = _ := (TopCat.toSSetObjEquiv_symm_naturality
        (X := (standardPuncturedPair d).snd) (f := f.unop)
        (g := standardAffineBoundarySimplex d n.unop.len x)).symm

/-- The unique nondegenerate simplex in the top dimension of a standard simplex. -/
def standardSimplexTopSimplexForLocalClass (n : ℕ) :
    (Δ[n] : SSet.{0}).obj (op (SimplexCategory.mk n)) :=
  SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))

/-- A top-dimensional face of the simplicial boundary of the standard `(n + 1)`-simplex. -/
def standardSphereBoundaryFaceSimplex (n : ℕ) (i : Fin (n + 2)) :
    (∂Δ[n + 1] : SSet.{0}).obj (op (SimplexCategory.mk n)) :=
  (SSet.boundary.ι i).app _ (standardSimplexTopSimplexForLocalClass n)

lemma standardSphereBoundaryFaceSimplex_nonDegenerate (n : ℕ) (i : Fin (n + 2)) :
    standardSphereBoundaryFaceSimplex n i ∈
      (∂Δ[n + 1] : SSet.{0}).nonDegenerate n := by
  apply (SSet.nonDegenerate_iff_of_mono
    (SSet.boundary (n + 1) : SSet.Subcomplex (Δ[n + 1] : SSet.{0})).ι _).mp
  rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono]
  change Mono (SimplexCategory.δ i)
  infer_instance

lemma standardSphereBoundaryFaceSimplex_injective (n : ℕ) :
    Function.Injective (standardSphereBoundaryFaceSimplex n) := by
  intro i j h
  apply SimplexCategory.δ_injective
  have h' := congrArg Subtype.val h
  change (SSet.stdSimplex.map (SimplexCategory.δ i)).app _
      (standardSimplexTopSimplexForLocalClass n) =
    (SSet.stdSimplex.map (SimplexCategory.δ j)).app _
      (standardSimplexTopSimplexForLocalClass n) at h'
  have key : ∀ k : Fin (n + 2), (SSet.stdSimplex.map (SimplexCategory.δ k)).app _
      (standardSimplexTopSimplexForLocalClass n) =
        SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ k) := fun k ↦ by
    simpa [standardSimplexTopSimplexForLocalClass] using
      (SSet.stdSimplex.objEquiv_symm_comp
        (𝟙 (SimplexCategory.mk n)) (SimplexCategory.δ k)).symm
  rw [key i, key j] at h'
  exact SSet.stdSimplex.objEquiv.symm.injective h'

lemma standardAffineBoundarySimplicialMap_face (n : ℕ) (i : Fin (n + 2)) :
    (standardAffineBoundarySimplicialMap (n + 1)).app _
        (standardSphereBoundaryFaceSimplex n i) =
      standardFaceSimplex n i := by
  apply ((standardPuncturedPair (n + 1)).snd.toSSetObjEquiv _).injective
  ext t
  apply Subtype.ext
  funext j
  rfl

/-- The chain map from a simplicial boundary to singular chains of punctured coordinate space. -/
def standardAffineBoundaryChainMap (d : ℕ) :
    ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)) ⟶
      (TopCat.toSSet.obj (standardPuncturedPair d).snd).chainComplex
        (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (standardAffineBoundarySimplicialMap d) (ModuleCat.of ℚ ℚ)

/-- A degreewise retraction from chains of the full simplex to chains of its boundary. Simplices
outside the boundary are sent to zero. -/
def standardSphereBoundaryChainRetractionComponent (d k : ℕ) :
    ((Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)).X k ⟶
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)).X k := by
  classical
  exact ((Δ[d] : SSet.{0}).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) k).desc
      (Cofan.mk _ (fun x ↦ if hx : x ∈ (SSet.boundary d).obj _ then
        (∂Δ[d] : SSet.{0}).ιChainComplex ⟨x, hx⟩ else 0))

lemma standardSphereBoundaryChainInclusion_comp_retraction (d k : ℕ) :
    (SSet.chainComplexMap
        (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
        (ModuleCat.of ℚ ℚ)).f k ≫
      standardSphereBoundaryChainRetractionComponent d k = 𝟙 _ := by
  classical
  apply (∂Δ[d] : SSet.{0}).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  change ((Δ[d] : SSet.{0}).chainComplexXCofan
      (ModuleCat.of ℚ ℚ) k).inj x.1 ≫
      standardSphereBoundaryChainRetractionComponent d k = _
  simp [standardSphereBoundaryChainRetractionComponent, x.2]
  congr

lemma standardSphereBoundaryChainInclusionComponent_mono (d k : ℕ) :
    Mono ((SSet.chainComplexMap
      (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
      (ModuleCat.of ℚ ℚ)).f k) := by
  constructor
  intro Z f g h
  let inc := (SSet.chainComplexMap
    (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
    (ModuleCat.of ℚ ℚ)).f k
  let ret := standardSphereBoundaryChainRetractionComponent d k
  have hret : inc ≫ ret = 𝟙 _ :=
    standardSphereBoundaryChainInclusion_comp_retraction d k
  calc
    f = (f ≫ inc) ≫ ret := by rw [Category.assoc, hret, Category.comp_id]
    _ = (g ≫ inc) ≫ ret := by rw [h]
    _ = g := by rw [Category.assoc, hret, Category.comp_id]

/-- The alternating top-face chain in the simplicial boundary. -/
def standardSphereSimplicialBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((∂Δ[n + 1] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)).X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val •
    (∂Δ[n + 1] : SSet.{0}).ιChainComplex
      (standardSphereBoundaryFaceSimplex n i)

lemma standardSphereSimplicialBoundaryChain_inclusion (n : ℕ) :
    standardSphereSimplicialBoundaryChain n ≫
        (SSet.chainComplexMap
          (SSet.boundary (n + 1) : SSet.Subcomplex (Δ[n + 1] : SSet.{0})).ι
          (ModuleCat.of ℚ ℚ)).f n =
      (Δ[n + 1] : SSet.{0}).ιChainComplex
          (standardSimplexTopSimplexForLocalClass (n + 1)) ≫
        ((Δ[n + 1] : SSet.{0}).chainComplex
          (ModuleCat.of ℚ ℚ)).d (n + 1) n := by
  rw [standardSphereSimplicialBoundaryChain, Preadditive.sum_comp,
    SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  rw [SSet.ι_chainComplexMap_f]
  rfl

lemma standardSphereSimplicialBoundaryChain_boundary_succ (n : ℕ) :
    standardSphereSimplicialBoundaryChain (n + 1) ≫
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
        (ModuleCat.of ℚ ℚ)).d (n + 1) n = 0 := by
  let f := SSet.chainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
    (ModuleCat.of ℚ ℚ)
  let : Mono (f.f n) := standardSphereBoundaryChainInclusionComponent_mono (n + 2) n
  rw [← cancel_mono (f.f n), Category.assoc, ← f.comm, ← Category.assoc,
    standardSphereSimplicialBoundaryChain_inclusion, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]
  simp

/-- The alternating facets as a cycle in every positive-dimensional standard simplicial
sphere. -/
def standardSphereSimplicialBoundaryCycle (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
        (ModuleCat.of ℚ ℚ)).cycles (n + 1) :=
  ((∂Δ[n + 2] : SSet.{0}).chainComplex
    (ModuleCat.of ℚ ℚ)).liftCycles
      (standardSphereSimplicialBoundaryChain (n + 1))
      ((ComplexShape.down ℕ).next (n + 1)) rfl
      (by
        rw [ChainComplex.next_nat_succ]
        exact standardSphereSimplicialBoundaryChain_boundary_succ n)

/-- The simplicial homology class of the alternating facets. -/
def standardSphereSimplicialBoundaryClass (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homology (n + 1) :=
  ((standardSphereSimplicialBoundaryCycle n ≫
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).homologyπ (n + 1)).hom) 1

/-- The alternating facet chain after passage to normalized chains. -/
def standardSphereSimplicialNormalizedBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      (standardSphereSuccNormalizedRationalChains n).X (n + 1) :=
  standardSphereSimplicialBoundaryChain (n + 1) ≫
    ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
      (ModuleCat.of ℚ ℚ)).f (n + 1)

/-- The coefficient functional of the zeroth oriented facet in normalized top chains. -/
def standardSphereSimplicialNormalizedBoundaryDetector (n : ℕ) :
    (standardSphereSuccNormalizedRationalChains n).X (n + 1) ⟶
      ModuleCat.of ℚ ℚ := by
  classical
  exact Cofan.IsColimit.desc
    ((∂Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
      (ModuleCat.of ℚ ℚ) (n + 1)) (fun x ↦
        if x.1 = standardSphereBoundaryFaceSimplex (n + 1) 0 then 𝟙 _ else 0)

lemma standardSphereSimplicialNormalizedBoundaryFace_detect
    (n : ℕ) (i : Fin (n + 3)) :
    (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
        (standardSphereBoundaryFaceSimplex (n + 1) i) ≫
      standardSphereSimplicialNormalizedBoundaryDetector n =
        if i = 0 then 𝟙 _ else 0 := by
  classical
  let x : (∂Δ[n + 2] : SSet.{0}).nonDegenerate (n + 1) :=
    ⟨standardSphereBoundaryFaceSimplex (n + 1) i,
      standardSphereBoundaryFaceSimplex_nonDegenerate (n + 1) i⟩
  change (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex x.1 ≫
      standardSphereSimplicialNormalizedBoundaryDetector n = _
  have hiff : standardSphereBoundaryFaceSimplex (n + 1) i =
      standardSphereBoundaryFaceSimplex (n + 1) 0 ↔ i = 0 :=
    (standardSphereBoundaryFaceSimplex_injective (n + 1)).eq_iff
  change ((∂Δ[n + 2] : SSet.{0}).cofanNormalizedChainComplex
      (ModuleCat.of ℚ ℚ) (n + 1)).inj x ≫
        standardSphereSimplicialNormalizedBoundaryDetector n = _
  rw [standardSphereSimplicialNormalizedBoundaryDetector,
    Cofan.IsColimit.fac]
  simp [x, hiff]

lemma standardSphereSimplicialNormalizedBoundaryChain_detect (n : ℕ) :
    standardSphereSimplicialNormalizedBoundaryChain n ≫
      standardSphereSimplicialNormalizedBoundaryDetector n = 𝟙 _ := by
  classical
  rw [standardSphereSimplicialNormalizedBoundaryChain,
    standardSphereSimplicialBoundaryChain, Preadditive.sum_comp,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, Category.assoc,
    SSet.ιChainComplex_toNormalizedChainComplex_f_assoc,
    standardSphereSimplicialNormalizedBoundaryFace_detect]
  rw [Finset.sum_eq_single (0 : Fin (n + 3))]
  · norm_num
  · intro i _ hi
    simp [hi]
  · simp

/-- The normalized alternating facet chain is nonzero in every positive sphere dimension. -/
lemma standardSphereSimplicialNormalizedBoundaryChain_ne_zero (n : ℕ) :
    standardSphereSimplicialNormalizedBoundaryChain n ≠ 0 := by
  intro h
  have hdet := standardSphereSimplicialNormalizedBoundaryChain_detect n
  rw [h, zero_comp] at hdet
  exact zero_ne_one (ConcreteCategory.congr_hom hdet 1)

lemma standardSphereSimplicialNormalizedBoundaryChain_boundary (n : ℕ) :
    standardSphereSimplicialNormalizedBoundaryChain n ≫
      (standardSphereSuccNormalizedRationalChains n).d (n + 1) n = 0 := by
  let K := (∂Δ[n + 2] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)
  let L := (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of ℚ ℚ)
  let q : K ⟶ L :=
    (∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of ℚ ℚ)
  change (standardSphereSimplicialBoundaryChain (n + 1) ≫ q.f (n + 1)) ≫
    L.d (n + 1) n = 0
  calc
    _ = standardSphereSimplicialBoundaryChain (n + 1) ≫
        (q.f (n + 1) ≫ L.d (n + 1) n) :=
      Category.assoc _ _ _
    _ = standardSphereSimplicialBoundaryChain (n + 1) ≫
        (K.d (n + 1) n ≫ q.f n) := by
      rw [← q.comm]
    _ = (standardSphereSimplicialBoundaryChain (n + 1) ≫
        K.d (n + 1) n) ≫ q.f n :=
      (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [standardSphereSimplicialBoundaryChain_boundary_succ, zero_comp]

/-- The normalized alternating facets as a top cycle. -/
def standardSphereSimplicialNormalizedBoundaryCycle (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      (standardSphereSuccNormalizedRationalChains n).cycles (n + 1) :=
  (standardSphereSuccNormalizedRationalChains n).liftCycles
    (standardSphereSimplicialNormalizedBoundaryChain n)
    ((ComplexShape.down ℕ).next (n + 1)) rfl (by
      rw [ChainComplex.next_nat_succ]
      exact standardSphereSimplicialNormalizedBoundaryChain_boundary n)

lemma standardSphereSimplicialNormalizedBoundaryCycle_inclusion (n : ℕ) :
    standardSphereSimplicialNormalizedBoundaryCycle n ≫
      (standardSphereSuccNormalizedRationalChains n).iCycles (n + 1) =
        standardSphereSimplicialNormalizedBoundaryChain n :=
  (standardSphereSuccNormalizedRationalChains n).liftCycles_i
    (standardSphereSimplicialNormalizedBoundaryChain n)
    ((ComplexShape.down ℕ).next (n + 1)) rfl _

/-- The normalized homology class of the alternating facets. -/
def standardSphereSimplicialNormalizedBoundaryClass (n : ℕ) :
    (standardSphereSuccNormalizedRationalChains n).homology (n + 1) :=
  ((standardSphereSimplicialNormalizedBoundaryCycle n ≫
    (standardSphereSuccNormalizedRationalChains n).homologyπ (n + 1)).hom) 1

/-- The explicit alternating-facet class is nonzero in normalized top homology. -/
lemma standardSphereSimplicialNormalizedBoundaryClass_ne_zero (n : ℕ) :
    standardSphereSimplicialNormalizedBoundaryClass n ≠ 0 := by
  let K := standardSphereSuccNormalizedRationalChains n
  have hd : K.d (n + 2) (n + 1) = 0 :=
    (standardSphereSucc_normalizedChains_aboveTop_isZero n).eq_of_src _ _
  let : IsIso (K.homologyπ (n + 1)) :=
    K.isIso_homologyπ (n + 2) (n + 1) (by simp) hd
  intro h
  have hcycle : (standardSphereSimplicialNormalizedBoundaryCycle n).hom 1 = 0 := by
    apply (ModuleCat.mono_iff_injective (K.homologyπ (n + 1))).mp inferInstance
    change standardSphereSimplicialNormalizedBoundaryClass n =
      (K.homologyπ (n + 1)).hom 0
    simpa only [map_zero] using h
  have hchain : (standardSphereSimplicialNormalizedBoundaryChain n).hom 1 = 0 := by
    have h' := congrArg (K.iCycles (n + 1)).hom hcycle
    rw [map_zero] at h'
    change ((standardSphereSimplicialNormalizedBoundaryCycle n ≫
      K.iCycles (n + 1)).hom) 1 = 0 at h'
    rw [standardSphereSimplicialNormalizedBoundaryCycle_inclusion] at h'
    exact h'
  have hdet := ConcreteCategory.congr_hom
    (standardSphereSimplicialNormalizedBoundaryChain_detect n) 1
  change (standardSphereSimplicialNormalizedBoundaryDetector n).hom
    ((standardSphereSimplicialNormalizedBoundaryChain n).hom 1) = 1 at hdet
  rw [hchain, map_zero] at hdet
  exact zero_ne_one hdet

/-- The explicit alternating-facet class spans normalized rational top homology. -/
lemma span_standardSphereSimplicialNormalizedBoundaryClass_eq_top (n : ℕ) :
    Submodule.span ℚ {standardSphereSimplicialNormalizedBoundaryClass n} = ⊤ := by
  let e := (standardSphereSuccNormalizedHomologyTopIsoRat n).toLinearEquiv
  have he : e (standardSphereSimplicialNormalizedBoundaryClass n) ≠ 0 :=
    e.map_ne_zero_iff.mpr (standardSphereSimplicialNormalizedBoundaryClass_ne_zero n)
  have hone : Submodule.span ℚ
      {e (standardSphereSimplicialNormalizedBoundaryClass n)} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff ℚ _).mpr fun q ↦
      ⟨q / e (standardSphereSimplicialNormalizedBoundaryClass n), by
        simpa only [smul_eq_mul] using div_mul_cancel₀ q he⟩
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]
  exact hone

lemma standardSphereSimplicialBoundaryCycle_normalization (n : ℕ) :
    standardSphereSimplicialBoundaryCycle n ≫
        HomologicalComplex.cyclesMap
          ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
            (ModuleCat.of ℚ ℚ)) (n + 1) =
      standardSphereSimplicialNormalizedBoundaryCycle n := by
  apply (cancel_mono
    ((standardSphereSuccNormalizedRationalChains n).iCycles (n + 1))).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i,
    standardSphereSimplicialNormalizedBoundaryCycle_inclusion, ← Category.assoc,
    standardSphereSimplicialBoundaryCycle, HomologicalComplex.liftCycles_i]
  rfl

lemma standardSphereSimplicialBoundaryClass_normalization (n : ℕ) :
    (HomologicalComplex.homologyMap
      ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
        (ModuleCat.of ℚ ℚ)) (n + 1)).hom
        (standardSphereSimplicialBoundaryClass n) =
      standardSphereSimplicialNormalizedBoundaryClass n := by
  let q := (∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of ℚ ℚ)
  have hmor :
      standardSphereSimplicialBoundaryCycle n ≫
          ((∂Δ[n + 2] : SSet.{0}).chainComplex
            (ModuleCat.of ℚ ℚ)).homologyπ (n + 1) ≫
          HomologicalComplex.homologyMap q (n + 1) =
        standardSphereSimplicialNormalizedBoundaryCycle n ≫
          (standardSphereSuccNormalizedRationalChains n).homologyπ (n + 1) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      standardSphereSimplicialBoundaryCycle_normalization]
  change ((standardSphereSimplicialBoundaryCycle n ≫
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
        (ModuleCat.of ℚ ℚ)).homologyπ (n + 1) ≫
      HomologicalComplex.homologyMap q (n + 1)).hom) 1 =
    ((standardSphereSimplicialNormalizedBoundaryCycle n ≫
      (standardSphereSuccNormalizedRationalChains n).homologyπ (n + 1)).hom) 1
  exact ConcreteCategory.congr_hom hmor 1

/-- The explicit alternating-facet class is nonzero in ordinary simplicial top homology. -/
lemma standardSphereSimplicialBoundaryClass_ne_zero (n : ℕ) :
    standardSphereSimplicialBoundaryClass n ≠ 0 := by
  intro h
  have hmap := standardSphereSimplicialBoundaryClass_normalization n
  rw [h, map_zero] at hmap
  exact standardSphereSimplicialNormalizedBoundaryClass_ne_zero n hmap.symm

/-- The explicit alternating-facet class spans ordinary rational simplicial top homology. -/
lemma span_standardSphereSimplicialBoundaryClass_eq_top (n : ℕ) :
    Submodule.span ℚ {standardSphereSimplicialBoundaryClass n} = ⊤ := by
  let e := (standardSphereSuccSimplicialHomologyTopIsoRat n).toLinearEquiv
  have he : e (standardSphereSimplicialBoundaryClass n) ≠ 0 :=
    e.map_ne_zero_iff.mpr (standardSphereSimplicialBoundaryClass_ne_zero n)
  have hone : Submodule.span ℚ {e (standardSphereSimplicialBoundaryClass n)} = ⊤ :=
    (Submodule.span_singleton_eq_top_iff ℚ _).mpr fun q ↦
      ⟨q / e (standardSphereSimplicialBoundaryClass n), by
        simpa only [smul_eq_mul] using div_mul_cancel₀ q he⟩
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]
  exact hone

/-- The alternating affine face chain in punctured coordinate space. -/
def standardPuncturedAffineBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((chainPairFunctor ℚ).obj (standardPuncturedPair (n + 1))).left.X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val • standardSubspaceFaceChain n i

lemma standardAffineBoundaryChainMap_standardSphereSimplicialBoundaryChain (n : ℕ) :
    standardSphereSimplicialBoundaryChain n ≫
        (standardAffineBoundaryChainMap (n + 1)).f n =
      standardPuncturedAffineBoundaryChain n := by
  rw [standardSphereSimplicialBoundaryChain, standardPuncturedAffineBoundaryChain,
    Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  congr 1
  change (∂Δ[n + 1] : SSet.{0}).ιChainComplex
      (standardSphereBoundaryFaceSimplex n i) ≫
        (SSet.chainComplexMap (standardAffineBoundarySimplicialMap (n + 1))
          (ModuleCat.of ℚ ℚ)).f n = _
  rw [SSet.ι_chainComplexMap_f, standardAffineBoundarySimplicialMap_face]
  rfl

end AlgebraicTopology.Singular
