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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCoverSmall

/-!
# Singular chains of a subspace

A singular simplex of a space factors through a subspace exactly when its topological image is
contained in that subspace, and the factorization is unique because the inclusion is injective.
This file turns that remark into the maps it is used through: a simplicial map into the singular
simplicial set lifts to the subspace whenever every represented simplex has image there, and a
single simplex lifts likewise.

Degreewise, the resulting lift retracts the integral chain inclusion of the subspace, so that
inclusion is a split monomorphism in every degree and is therefore cancellable on the left.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

/-- A singular simplex factors through a subspace exactly when its topological image is
contained in that subspace. -/
lemma singularSimplex_mem_range_subset
    (X : TopCat.{0}) (s : Set X) {n : SimplexCategoryᵒᵖ}
    (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X s))).obj n ↔
      Set.range (X.toSSetObjEquiv n x) ⊆ s := by
  simp only [Subfunctor.range_obj]
  constructor
  · rintro ⟨y, rfl⟩ _ ⟨t, rfl⟩
    exact (TopCat.of s).toSSetObjEquiv n y t |>.2
  · intro h
    let f : C(stdSimplex ℝ (Fin (n.unop.len + 1)), TopCat.of s) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv n x t, h ⟨t, rfl⟩⟩,
        Continuous.subtype_mk (X.toSSetObjEquiv n x).continuous _⟩
    refine ⟨((TopCat.of s).toSSetObjEquiv n).symm f, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext t
    rfl

/-- A simplicial map to a singular simplicial set lifts to a topological subspace when every
represented continuous simplex has image in that subspace. -/
def singularSimplicialMapLiftToSubset
    (X : SSet.{0}) (Y : TopCat.{0}) (s : Set Y)
    (f : X ⟶ TopCat.toSSet.obj Y)
    (hf : ∀ (n : SimplexCategoryᵒᵖ) (x : X.obj n),
      Set.range (Y.toSSetObjEquiv n (f.app n x)) ⊆ s) :
    X ⟶ TopCat.toSSet.obj (TopCat.of s) where
  app n := ↾ fun x ↦
    ((TopCat.of s).toSSetObjEquiv n).symm
      ⟨fun t ↦ ⟨Y.toSSetObjEquiv n (f.app n x) t,
          hf n x ⟨t, rfl⟩⟩,
        Continuous.subtype_mk
          (Y.toSSetObjEquiv n (f.app n x)).continuous _⟩
  naturality n m g := by
    ext x
    apply ((TopCat.of s).toSSetObjEquiv m).injective
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    change (Y.toSSetObjEquiv m (f.app m (X.map g x))) t =
      (Y.toSSetObjEquiv m
        ((TopCat.toSSet.obj Y).map g (f.app n x))) t
    have h := ConcreteCategory.congr_hom (f.naturality g) x
    apply_fun fun z ↦ Y.toSSetObjEquiv m z t at h
    simpa only [ConcreteCategory.comp_apply] using h

@[reassoc (attr := simp)]
lemma singularSimplicialMapLiftToSubset_comp_inclusion
    (X : SSet.{0}) (Y : TopCat.{0}) (s : Set Y)
    (f : X ⟶ TopCat.toSSet.obj Y)
    (hf : ∀ (n : SimplexCategoryᵒᵖ) (x : X.obj n),
      Set.range (Y.toSSetObjEquiv n (f.app n x)) ⊆ s) :
    singularSimplicialMapLiftToSubset X Y s f hf ≫
        TopCat.toSSet.map (topologicalSubsetInclusion Y s) = f := by
  ext n x
  apply (Y.toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  change ((((TopCat.of s).toSSetObjEquiv n)
    ((singularSimplicialMapLiftToSubset X Y s f hf).app n x)) t).1 =
      (Y.toSSetObjEquiv n (f.app n x)) t
  rfl

/-- Maps into a topological subspace are equal when their composites with the subspace
inclusion are equal. -/
lemma singularSimplicialMapToSubset_ext
    (X : SSet.{0}) (Y : TopCat.{0}) (s : Set Y)
    (f g : X ⟶ TopCat.toSSet.obj (TopCat.of s))
    (h : f ≫ TopCat.toSSet.map (topologicalSubsetInclusion Y s) =
      g ≫ TopCat.toSSet.map (topologicalSubsetInclusion Y s)) : f = g := by
  ext n x
  apply ((TopCat.of s).toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (Y.toSSetObjEquiv n
      ((TopCat.toSSet.map (topologicalSubsetInclusion Y s)).app n (f.app n x))) t =
    (Y.toSSetObjEquiv n
      ((TopCat.toSSet.map (topologicalSubsetInclusion Y s)).app n (g.app n x))) t
  have hx := congrArg (fun k : X ⟶ TopCat.toSSet.obj Y ↦ k.app n x) h
  change (TopCat.toSSet.map (topologicalSubsetInclusion Y s)).app n (f.app n x) =
    (TopCat.toSSet.map (topologicalSubsetInclusion Y s)).app n (g.app n x) at hx
  exact congrArg (fun z ↦ Y.toSSetObjEquiv n z t) hx

/-- A singular simplex whose image lies in a subspace, regarded as a simplex of that
subspace. -/
def singularSimplexLiftToSubset
    (X : TopCat.{0}) (s : Set X) {n : SimplexCategoryᵒᵖ}
    (x : (TopCat.toSSet.obj X).obj n)
    (hx : Set.range (X.toSSetObjEquiv n x) ⊆ s) :
    (TopCat.toSSet.obj (TopCat.of s)).obj n :=
  ((TopCat.of s).toSSetObjEquiv n).symm
    ⟨fun t ↦ ⟨X.toSSetObjEquiv n x t, hx ⟨t, rfl⟩⟩,
      Continuous.subtype_mk (X.toSSetObjEquiv n x).continuous _⟩

@[simp]
lemma singularSimplexLiftToSubset_comp_inclusion
    (X : TopCat.{0}) (s : Set X) {n : SimplexCategoryᵒᵖ}
    (x : (TopCat.toSSet.obj X).obj n)
    (hx : Set.range (X.toSSetObjEquiv n x) ⊆ s) :
    (TopCat.toSSet.map (topologicalSubsetInclusion X s)).app n
      (singularSimplexLiftToSubset X s x hx) = x := by
  apply (X.toSSetObjEquiv n).injective
  ext t
  rfl

/-- A degreewise retraction of integral singular chains along a topological subspace
inclusion.  It sends a simplex outside the subspace to zero. -/
def singularSubsetIntegralChainRetractionComponent
    (X : TopCat.{0}) (s : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of s)).chainComplex
        (AddCommGrpCat.of ℤ)).X n := by
  classical
  exact (TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (AddCommGrpCat.of ℤ) n |>.desc
      (Cofan.mk _ (fun x ↦
        if hx : Set.range ((X.toSSetObjEquiv _ x)) ⊆ s then
          (TopCat.toSSet.obj (TopCat.of s)).ιChainComplex
            (singularSimplexLiftToSubset X s x hx)
        else 0))

set_option backward.isDefEq.respectTransparency false in
lemma singularSubsetIntegralChainInclusion_comp_retraction
    (X : TopCat.{0}) (s : Set X) (n : ℕ) :
    (SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion X s))
        (AddCommGrpCat.of ℤ)).f n ≫
      singularSubsetIntegralChainRetractionComponent X s n = 𝟙 _ := by
  apply (TopCat.toSSet.obj (TopCat.of s)).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  change ((TopCat.toSSet.obj X).chainComplexXCofan
      (AddCommGrpCat.of ℤ) n).inj
        ((TopCat.toSSet.map (topologicalSubsetInclusion X s)).app _ x) ≫
      singularSubsetIntegralChainRetractionComponent X s n = _
  have hx : Set.range (X.toSSetObjEquiv _
      ((TopCat.toSSet.map (topologicalSubsetInclusion X s)).app _ x)) ⊆ s := by
    rintro _ ⟨t, rfl⟩
    exact ((TopCat.of s).toSSetObjEquiv _ x t).2
  simp [singularSubsetIntegralChainRetractionComponent, hx]
  congr

/-- Integral singular chains of a topological subspace inject degreewise into ambient
singular chains. -/
lemma singularSubsetIntegralChainInclusionComponent_mono
    (X : TopCat.{0}) (s : Set X) (n : ℕ) :
    Mono ((SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubsetInclusion X s))
      (AddCommGrpCat.of ℤ)).f n) := by
  constructor
  intro Z f g h
  let inc := (SSet.chainComplexMap
    (TopCat.toSSet.map (topologicalSubsetInclusion X s))
    (AddCommGrpCat.of ℤ)).f n
  let ret := singularSubsetIntegralChainRetractionComponent X s n
  have hret : inc ≫ ret = 𝟙 _ :=
    singularSubsetIntegralChainInclusion_comp_retraction X s n
  calc
    f = (f ≫ inc) ≫ ret := by rw [Category.assoc, hret, Category.comp_id]
    _ = (g ≫ inc) ≫ ret := by rw [h]
    _ = g := by rw [Category.assoc, hret, Category.comp_id]

end AlgebraicTopology.Singular
