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

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Rational top homology of simplicial spheres

This file computes the top rational simplicial homology of the boundary of every positive-
dimensional standard simplex. The proof compares normalized chains below the top dimension with
the full simplex and uses its extra degeneracy.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial HomologicalComplex
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- Normalized rational chains of the standard `(n + 2)`-simplex. -/
abbrev standardSimplexSuccNormalizedRationalChains (n : ℕ) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of ℚ ℚ)

/-- Normalized rational chains of the boundary of the standard `(n + 2)`-simplex. Its
realization is an `(n + 1)`-sphere. -/
abbrev standardSphereSuccNormalizedRationalChains (n : ℕ) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of ℚ ℚ)

/-- Normalized chains of a standard simplex are exact in every positive degree. -/
lemma standardSimplexSucc_normalizedChains_exactAt (n k : ℕ) (hk : k ≠ 0) :
    (standardSimplexSuccNormalizedRationalChains n).ExactAt k := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk (n + 2))).map ((sigmaConst.obj (ModuleCat.of ℚ ℚ)))
  let e := ed.homotopyEquiv
  have hchains : ((Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of ℚ ℚ)).ExactAt k :=
    (exactAt_iff_of_quasiIsoAt e.hom k).mpr (exactAt_single_obj _ _ _ _ hk)
  exact (exactAt_iff_of_quasiIsoAt
    ((Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of ℚ ℚ)) k).mp hchains

/-- Below dimension `n + 2`, regard a nondegenerate simplex of the full standard simplex as a
simplex of its boundary. -/
def standardSimplexSuccNormalizedChainsToBoundary (n k : ℕ) (hk : k < n + 2) :
    (standardSimplexSuccNormalizedRationalChains n).X k ⟶
      (standardSphereSuccNormalizedRationalChains n).X k :=
  ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (ModuleCat.of ℚ ℚ) k).desc
      (Cofan.mk _ (fun x ↦
        (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          ⟨x.1, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩))

lemma ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary
    (n k : ℕ) (hk : k < n + 2)
    (x : (Δ[n + 2] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk k)))
    (hx : x ∈ (Δ[n + 2] : SSet.{0}).nonDegenerate k) :
    (Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex x ≫
        standardSimplexSuccNormalizedChainsToBoundary n k hk =
      (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
        ⟨x, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩ :=
  ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (ModuleCat.of ℚ ℚ) k).fac
      (Cofan.mk _ (fun x ↦
        (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          ⟨x.1, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩)) ⟨x, hx⟩

/-- Below its top simplex, the normalized groups of a standard simplex and its boundary agree. -/
def standardSphereSuccNormalizedChainsXIsoStandard
    (n k : ℕ) (hk : k < n + 2) :
    (standardSphereSuccNormalizedRationalChains n).X k ≅
      (standardSimplexSuccNormalizedRationalChains n).X k where
  hom := (SSet.normalizedChainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
      (ModuleCat.of ℚ ℚ)).f k
  inv := standardSimplexSuccNormalizedChainsToBoundary n k hk
  hom_inv_id := by
    apply (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f, Category.comp_id]
    have hx' : x.1 ∈ (Δ[n + 2] : SSet.{0}).nonDegenerate k := by
      rwa [← (SSet.boundary (n + 2)).mem_nonDegenerate_iff x]
    convert ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary
      n k hk x.1 hx' using 1 <;> try rfl
  inv_hom_id := by
    apply (Δ[n + 2] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, Category.comp_id]
    rw [ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary n k hk x hx]
    calc
      _ = (Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          (((SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι).app _
            ⟨x, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩) :=
        SSet.ι_normalizedChainComplexMap_f
          (f := (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι)
          (R := ModuleCat.of ℚ ℚ) _
      _ = _ := by congr

/-- The top cycle kernels of the boundary and full standard simplex agree. -/
def standardSphereSuccTopCyclesIsoStandardSimplexSuccTopCycles (n : ℕ) :
    kernel ((standardSphereSuccNormalizedRationalChains n).d (n + 1) n) ≅
      kernel ((standardSimplexSuccNormalizedRationalChains n).d (n + 1) n) := by
  let f := SSet.normalizedChainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
      (ModuleCat.of ℚ ℚ)
  let eTop := standardSphereSuccNormalizedChainsXIsoStandard n (n + 1) (by lia)
  let eBelow := standardSphereSuccNormalizedChainsXIsoStandard n n (by lia)
  letI : IsIso (f.f (n + 1)) := eTop.isIso_hom
  letI : IsIso (f.f n) := eBelow.isIso_hom
  let φ := (shortComplexFunctor' (ModuleCat ℚ) (ComplexShape.down ℕ)
    (n + 2) (n + 1) n).map f
  letI : IsIso φ.τ₂ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  letI : IsIso φ.τ₃ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  exact ((standardSphereSuccNormalizedRationalChains n).sc'
      (n + 2) (n + 1) n).cyclesIsoKernel.symm ≪≫
    asIso (ShortComplex.cyclesMap φ) ≪≫
      ((standardSimplexSuccNormalizedRationalChains n).sc'
        (n + 2) (n + 1) n).cyclesIsoKernel

/-- The top normalized group of a standard simplex is canonically one-dimensional. -/
def standardSimplexSuccNormalizedChainsXTopIsoRat (n : ℕ) :
    (standardSimplexSuccNormalizedRationalChains n).X (n + 2) ≅ ModuleCat.of ℚ ℚ := by
  let top : (Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2) :=
    ⟨SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk (n + 2))),
      SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate (n + 2)⟩
  letI : Unique ((Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2)) :=
    { default := top
      uniq := fun x ↦ by
        apply Subtype.ext
        have hx' : x.1 ∈
            ({SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk (n + 2)))} :
              Set ((Δ[n + 2] : SSet.{0}).obj
                (Opposite.op (SimplexCategory.mk (n + 2))))) := by
          rw [← SSet.stdSimplex.nonDegenerate_top_dim]
          exact x.2
        simpa [top] using hx' }
  exact IsColimit.coconePointUniqueUpToIso
    ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
      (ModuleCat.of ℚ ℚ) (n + 2))
    (Cofan.isColimitMkOfUnique (Iso.refl (ModuleCat.of ℚ ℚ))
      ((Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2)))

/-- The top differential of a full standard simplex is a monomorphism. -/
lemma standardSimplexSucc_normalized_d_top_mono (n : ℕ) :
    Mono ((standardSimplexSuccNormalizedRationalChains n).d (n + 2) (n + 1)) := by
  have hTop := standardSimplexSucc_normalizedChains_exactAt n (n + 2) (by lia)
  have hTop' : ((standardSimplexSuccNormalizedRationalChains n).sc'
      (n + 3) (n + 2) (n + 1)).Exact :=
    ShortComplex.exact_of_iso
      ((standardSimplexSuccNormalizedRationalChains n).isoSc'
        (n + 3) (n + 2) (n + 1) (by simp) (by simp)) hTop
  have hAbove : IsZero ((standardSimplexSuccNormalizedRationalChains n).X (n + 3)) :=
    (Δ[n + 2] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
      (ModuleCat.of ℚ ℚ) (n + 3) (n + 3)
  exact hTop'.mono_g (hAbove.eq_of_src _ _)

/-- Exactness identifies the top group of a full standard simplex with the cycle kernel one
degree below. -/
def standardSimplexSuccNormalizedChainsXTopIsoTopCycles (n : ℕ) :
    (standardSimplexSuccNormalizedRationalChains n).X (n + 2) ≅
      kernel ((standardSimplexSuccNormalizedRationalChains n).d (n + 1) n) := by
  letI : Mono ((standardSimplexSuccNormalizedRationalChains n).d (n + 2) (n + 1)) :=
    standardSimplexSucc_normalized_d_top_mono n
  have h := standardSimplexSucc_normalizedChains_exactAt n (n + 1) (by lia)
  have h' : ((standardSimplexSuccNormalizedRationalChains n).sc'
      (n + 2) (n + 1) n).Exact :=
    ShortComplex.exact_of_iso
      ((standardSimplexSuccNormalizedRationalChains n).isoSc'
        (n + 2) (n + 1) n (by simp) (by simp)) h
  letI : Mono ((standardSimplexSuccNormalizedRationalChains n).sc'
      (n + 2) (n + 1) n).f := standardSimplexSucc_normalized_d_top_mono n
  exact IsLimit.conePointUniqueUpToIso h'.fIsKernel
    (limit.isLimit (parallelPair
      ((standardSimplexSuccNormalizedRationalChains n).d (n + 1) n) 0))

/-- The top normalized cycle kernel of a standard simplicial sphere is one-dimensional. -/
def standardSphereSuccTopCyclesIsoRat (n : ℕ) :
    kernel ((standardSphereSuccNormalizedRationalChains n).d (n + 1) n) ≅
      ModuleCat.of ℚ ℚ :=
  standardSphereSuccTopCyclesIsoStandardSimplexSuccTopCycles n ≪≫
    (standardSimplexSuccNormalizedChainsXTopIsoTopCycles n).symm ≪≫
      standardSimplexSuccNormalizedChainsXTopIsoRat n

/-- The normalized boundary has no group above its top dimension. -/
lemma standardSphereSucc_normalizedChains_aboveTop_isZero (n : ℕ) :
    IsZero ((standardSphereSuccNormalizedRationalChains n).X (n + 2)) :=
  (∂Δ[n + 2] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
    (ModuleCat.of ℚ ℚ) (n + 2) (n + 2)

/-- Top normalized homology of the boundary of a standard simplex is its top cycle kernel. -/
def standardSphereSuccNormalizedHomologyTopIsoTopCycles (n : ℕ) :
    (standardSphereSuccNormalizedRationalChains n).homology (n + 1) ≅
      kernel ((standardSphereSuccNormalizedRationalChains n).d (n + 1) n) := by
  let K := standardSphereSuccNormalizedRationalChains n
  let S := K.sc' (n + 2) (n + 1) n
  have hf : S.f = 0 :=
    (standardSphereSucc_normalizedChains_aboveTop_isZero n).eq_of_src _ _
  exact K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel

/-- Normalized rational top homology of a positive-dimensional standard simplicial sphere is
one-dimensional. -/
def standardSphereSuccNormalizedHomologyTopIsoRat (n : ℕ) :
    (standardSphereSuccNormalizedRationalChains n).homology (n + 1) ≅
      ModuleCat.of ℚ ℚ :=
  standardSphereSuccNormalizedHomologyTopIsoTopCycles n ≪≫
    standardSphereSuccTopCyclesIsoRat n

/-- Rational simplicial homology of the boundary of the standard `(n + 2)`-simplex in degree
`n + 1` is one-dimensional. -/
def standardSphereSuccSimplicialHomologyTopIsoRat (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex (ModuleCat.of ℚ ℚ)).homology (n + 1) ≅
      ModuleCat.of ℚ ℚ :=
  isoOfQuasiIsoAt
      ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of ℚ ℚ)) (n + 1) ≪≫
    standardSphereSuccNormalizedHomologyTopIsoRat n

end AlgebraicTopology.Singular
