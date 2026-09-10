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

public import FormalConjecturesForMathlib.AlgebraicTopology.SingularSubdivision

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Low-dimensional barycentric fundamental chains

This file constructs the first actual components of the barycentric subdivision chain operator.
The construction starts from the vertex of `sd Δ[0]` represented by the singleton chain and
uses Yoneda naturality to associate a subdivided vertex to every vertex of a simplicial set.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace AlgebraicTopology.Singular

/-- A singleton, regarded as a nonempty finite chain. -/
public noncomputable def nonemptyFiniteChainSingleton
    {X : Type*} [LinearOrder X] (x : X) : NonemptyFiniteChains X where
  finset := {x}
  comparable := by simp

@[simp]
public theorem nonemptyFiniteChainSingleton_finset
    {X : Type*} [LinearOrder X] (x : X) :
    (nonemptyFiniteChainSingleton x).finset = {x} :=
  rfl

/-- A specified nonempty finset in a linear order, regarded as a finite chain.

This constructor is shared by the all-degree barycentric development; unlike the removed
degree-one scaffolding, it is part of that file's live API. -/
public noncomputable def nonemptyFiniteChainOfFinset
    {X : Type*} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    NonemptyFiniteChains X where
  finset := s
  nonempty := hs
  comparable a b := le_total a b

/-- The vertex of the subdivision model of `Δ[0]` represented by its singleton vertex chain. -/
public noncomputable def subdividedZeroSimplexVertex :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 0)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (nonemptyFiniteChainSingleton (ULift.up (0 : Fin 1)))

/-- The corresponding vertex of Mathlib's left-Kan-extension model `sd Δ[0]`. -/
public noncomputable def subdividedStandardZeroVertex :
    (SSet.sd.obj (Δ[0] : SSet.{0})).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 0) |>.app _
    subdividedZeroSimplexVertex

/-- Every vertex of a simplicial set determines its canonical vertex after subdivision. -/
public noncomputable def barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (SSet.sd.obj X).obj (Opposite.op (SimplexCategory.mk 0)) :=
  (SSet.sd.map (SSet.yonedaEquiv.symm x)).app _ subdividedStandardZeroVertex

/-- The last-vertex map sends the canonical subdivided vertex of `Δ[0]` to its unique
vertex. -/
public theorem subdivisionLastVertex_subdividedStandardZeroVertex :
    (subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
        subdividedStandardZeroVertex =
      SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 0)) := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The last-vertex map is a left inverse to barycentric subdivision on vertices. -/
public theorem subdivisionLastVertex_barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (subdivisionLastVertex.app X).app _ (barycentricSubdivisionVertex X x) = x := by
  let f : (Δ[0] : SSet.{0}) ⟶ X := SSet.yonedaEquiv.symm x
  have hx := ConcreteCategory.congr_hom (NatTrans.congr_app
    (subdivisionLastVertex.naturality f)
    (Opposite.op (SimplexCategory.mk 0))) subdividedStandardZeroVertex
  change (subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) =
    f.app _ ((subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
      subdividedStandardZeroVertex) at hx
  rw [subdivisionLastVertex_subdividedStandardZeroVertex] at hx
  change (subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) = x
  rw [hx]
  change X.map (𝟙 (Opposite.op (SimplexCategory.mk 0))) x = x
  simp

/-- Canonical subdivided vertices are natural in maps of simplicial sets. -/
public theorem barycentricSubdivisionVertex_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    barycentricSubdivisionVertex Y (f.app _ x) =
      (SSet.sd.map f).app _ (barycentricSubdivisionVertex X x) := by
  rw [barycentricSubdivisionVertex, barycentricSubdivisionVertex,
    ← SSet.yonedaEquiv_symm_comp]
  have h := SSet.sd.map_comp (SSet.yonedaEquiv.symm x) f
  have h₀ := NatTrans.congr_app h (Opposite.op (SimplexCategory.mk 0))
  exact ConcreteCategory.congr_hom h₀ subdividedStandardZeroVertex

/-- The degree-zero component of barycentric subdivision on integral simplicial chains. -/
public noncomputable def barycentricSubdivisionChainMapZero (X : SSet.{0}) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X 0 ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 0 :=
  Sigma.desc (fun x ↦ (SSet.sd.obj X).ιChainComplex
    (barycentricSubdivisionVertex X x))

@[reassoc (attr := simp)]
public theorem iota_barycentricSubdivisionChainMapZero
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    X.ιChainComplex x ≫ barycentricSubdivisionChainMapZero X =
      (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) := by
  apply Sigma.ι_desc

/-- In degree zero, barycentric subdivision followed by last vertex is exactly the identity. -/
public theorem barycentricSubdivisionChainMapZero_comp_lastVertex
    (X : SSet.{0}) :
    barycentricSubdivisionChainMapZero X ≫
        (subdivisionLastVertexChainMap X).f 0 =
      𝟙 ((X.chainComplex (AddCommGrpCat.of ℤ)).X 0) := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapZero]
  change (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) ≫
      (SSet.chainComplexMap (subdivisionLastVertex.app X)
        (AddCommGrpCat.of ℤ)).f 0 = _
  rw [SSet.ι_chainComplexMap_f,
    subdivisionLastVertex_barycentricSubdivisionVertex]
  simp

/-- The degree-zero barycentric subdivision maps are natural. -/
public theorem barycentricSubdivisionChainMapZero_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f 0 ≫
        barycentricSubdivisionChainMapZero Y =
      barycentricSubdivisionChainMapZero X ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f 0 := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_barycentricSubdivisionChainMapZero]
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapZero,
    SSet.ι_chainComplexMap_f, barycentricSubdivisionVertex_naturality]

end AlgebraicTopology.Singular
