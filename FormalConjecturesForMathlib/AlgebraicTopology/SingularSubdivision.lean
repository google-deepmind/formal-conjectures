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
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# The last-vertex map for simplicial subdivision

Mathlib defines barycentric subdivision as a left Kan extension, but currently does not include
the classical last-vertex natural transformation.  This file begins that construction at its
finite-poset source: a nonempty finite chain is sent to its greatest vertex.  The maximum map is
monotone and natural in monotone maps between finite linear orders, so taking nerves gives the
last-vertex map on the subdivided standard simplices.
-/

@[expose] public section

noncomputable section

open CategoryTheory PartialOrder

namespace AlgebraicTopology.Singular

universe u

/-- A nonempty finite chain in a linear order is sent monotonically to its greatest element. -/
public noncomputable def nonemptyFiniteChainMaximum (X : Type*) [LinearOrder X] :
    NonemptyFiniteChains X →o X where
  toFun A := A.finset.max' A.nonempty
  monotone' A _ h := Finset.max'_subset A.nonempty h

@[simp]
public theorem nonemptyFiniteChainMaximum_apply
    {X : Type*} [LinearOrder X] (A : NonemptyFiniteChains X) :
    nonemptyFiniteChainMaximum X A = A.finset.max' A.nonempty :=
  rfl

/-- Taking the maximum commutes with a monotone map between finite linear orders. -/
public theorem nonemptyFiniteChainMaximum_map
    {X Y : Type*} [LinearOrder X] [LinearOrder Y]
    (f : X →o Y) (A : NonemptyFiniteChains X) :
    nonemptyFiniteChainMaximum Y (A.map f) = f (nonemptyFiniteChainMaximum X A) := by
  rw [nonemptyFiniteChainMaximum_apply, nonemptyFiniteChainMaximum_apply]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff A f y).1 hy
    exact f.monotone (Finset.le_max' A.finset x hx)
  · apply Finset.le_max'
    exact (NonemptyFiniteChains.mem_map_iff A f _).2
      ⟨A.finset.max' A.nonempty, A.finset.max'_mem A.nonempty, rfl⟩

/-- The maximum-vertex morphism from chains in the vertex poset of a standard simplex. -/
public noncomputable def simplexSubdivisionMaximum (n : SimplexCategory) :
    (SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor).obj n ⟶
      SimplexCategory.toPartOrd.{u}.obj n :=
  PartOrd.ofHom
    (nonemptyFiniteChainMaximum (ULift.{u} (Fin (n.len + 1))))

/-- The underlying vertex map of `toPartOrd.map f` is monotone for the canonical linear orders
on the lifted finite ordinals. -/
public theorem simplexToPartOrdMap_monotone {n m : SimplexCategory} (f : n ⟶ m)
    {i j : ULift.{u} (Fin (n.len + 1))} (h : i ≤ j) :
    SimplexCategory.toPartOrd.{u}.map f i ≤
      SimplexCategory.toPartOrd.{u}.map f j := by
  induction i with
  | up i =>
    induction j with
    | up j =>
      exact f.toOrderHom.monotone h

/-- Maximum vertex is natural in morphisms of the simplex category. -/
public noncomputable def simplexSubdivisionMaximumNatTrans :
    SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor ⟶
      SimplexCategory.toPartOrd.{u} where
  app := simplexSubdivisionMaximum
  naturality := by
    intro n m f
    apply PartOrd.ext
    intro A
    rw [PartOrd.comp_apply, PartOrd.comp_apply]
    change NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) at A
    change nonemptyFiniteChainMaximum (ULift.{u} (Fin (m.len + 1)))
        (A.map (SimplexCategory.toPartOrd.{u}.map f).hom) =
      (SimplexCategory.toPartOrd.{u}.map f).hom
        (nonemptyFiniteChainMaximum (ULift.{u} (Fin (n.len + 1))) A)
    exact nonemptyFiniteChainMaximum_map _ A

/-- Taking nerves gives the last-vertex map on the subdivision model of standard simplices. -/
public noncomputable def simplexSubdivisionLastVertexToNerve :
    SimplexCategory.sd.{u} ⟶
      SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nerveFunctor :=
  Functor.whiskerRight simplexSubdivisionMaximumNatTrans PartOrd.nerveFunctor

/-- The objectwise identification of the standard simplex with the nerve of its vertex order is
natural in the simplex category. -/
public noncomputable def standardSimplexNerveIso :
    SSet.stdSimplex.{u} ≅
      SimplexCategory.toPartOrd.{u} ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n ↦ SSet.stdSimplex.isoNerve n.len) fun _ ↦ rfl

/-- The last-vertex map from the subdivision model of standard simplices to standard simplices. -/
public noncomputable def simplexSubdivisionLastVertex :
    SimplexCategory.sd.{u} ⟶ SSet.stdSimplex.{u} :=
  simplexSubdivisionLastVertexToNerve ≫ standardSimplexNerveIso.inv

/-- The last-vertex map, viewed with the codomain required by the left Kan extension universal
property. -/
public noncomputable def simplexSubdivisionLastVertexExtension :
    SimplexCategory.sd.{u} ⟶
      SSet.stdSimplex.{u} ⋙ Functor.id SSet.{u} :=
  simplexSubdivisionLastVertex.{u} ≫
    (Functor.rightUnitor SSet.stdSimplex.{u}).inv

/-- The global last-vertex natural transformation `sd X ⟶ X`, obtained from the defining left
Kan extension universal property of simplicial subdivision. -/
public noncomputable def subdivisionLastVertex :
    SSet.sd.{u} ⟶ Functor.id SSet.{u} :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv
    (Functor.id SSet.{u})
    simplexSubdivisionLastVertexExtension.{u}

/-- On subdivided standard simplices, the global last-vertex map restricts to the maximum-vertex
construction above. -/
public theorem subdivisionLastVertex_standardSimplex (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫
        (subdivisionLastVertex.{u}.app (SSet.stdSimplex.obj n)) =
      simplexSubdivisionLastVertex.{u}.app n :=
  SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv
    (Functor.id SSet.{u}) simplexSubdivisionLastVertexExtension.{u} n

/-- The chain map induced by the last-vertex map of a simplicial set. -/
public noncomputable def subdivisionLastVertexChainMap (X : SSet.{0}) :
    (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      X.chainComplex (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap (subdivisionLastVertex.app X) (AddCommGrpCat.of ℤ)

/-- The last-vertex chain maps are natural in the simplicial set. -/
@[reassoc]
public theorem subdivisionLastVertexChainMap_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ) ≫
        subdivisionLastVertexChainMap Y =
      subdivisionLastVertexChainMap X ≫
        SSet.chainComplexMap f (AddCommGrpCat.of ℤ) := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (SSet.sd.map f) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (subdivisionLastVertex.app Y) =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (subdivisionLastVertex.app X) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map f
  rw [← Functor.map_comp, ← Functor.map_comp, subdivisionLastVertex.naturality]
  rfl

/-- The concrete condition that every simplex produced by the last-vertex map lands in a chosen
subcomplex. -/
public def SubdivisionLastVertexLandsInSubcomplex {X : SSet.{0}}
    (A : X.Subcomplex) : Prop :=
  SSet.Subcomplex.range (subdivisionLastVertex.app X) ≤ A

/-- If last vertices land in `A`, the last-vertex map itself lifts coherently through `A`. -/
public noncomputable def subdivisionLastVertexLiftToSubcomplex
    {X : SSet.{0}} (A : X.Subcomplex)
    (h : SubdivisionLastVertexLandsInSubcomplex A) :
    SSet.sd.obj X ⟶ A :=
  SSet.Subcomplex.lift (subdivisionLastVertex.app X) h

@[reassoc (attr := simp)]
public theorem subdivisionLastVertexLiftToSubcomplex_comp_inclusion
    {X : SSet.{0}} (A : X.Subcomplex)
    (h : SubdivisionLastVertexLandsInSubcomplex A) :
    subdivisionLastVertexLiftToSubcomplex A h ≫ A.ι =
      subdivisionLastVertex.app X :=
  SSet.Subcomplex.lift_ι _ _

/-- The lifted last-vertex chain map into a chosen subcomplex. -/
public noncomputable def subdivisionLastVertexLiftChainMap
    {X : SSet.{0}} (A : X.Subcomplex)
    (h : SubdivisionLastVertexLandsInSubcomplex A) :
    (SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (A : SSet).chainComplex (AddCommGrpCat.of ℤ) :=
  SSet.chainComplexMap (subdivisionLastVertexLiftToSubcomplex A h)
    (AddCommGrpCat.of ℤ)

/-- The lifted chain map factors the last-vertex chain map through subcomplex chains. -/
@[reassoc]
public theorem subdivisionLastVertexLiftChainMap_comp_inclusion
    {X : SSet.{0}} (A : X.Subcomplex)
    (h : SubdivisionLastVertexLandsInSubcomplex A) :
    subdivisionLastVertexLiftChainMap A h ≫
        SSet.chainComplexMap A.ι (AddCommGrpCat.of ℤ) =
      subdivisionLastVertexChainMap X := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (subdivisionLastVertexLiftToSubcomplex A h) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map A.ι =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (subdivisionLastVertex.app X)
  rw [← Functor.map_comp, subdivisionLastVertexLiftToSubcomplex_comp_inclusion]

section CoverSmallSubdivision

variable {i : Type} (X : TopCat) (U : i → Set X)

/-- The precise one-subdivision smallness condition for a topological cover. -/
public def OneSubdivisionMakesCoverSmall : Prop :=
  SubdivisionLastVertexLandsInSubcomplex (coverSmallSingularSubcomplex X U)

/-- Under the concrete one-subdivision smallness condition, last-vertex chains land in the
cover-small singular chain complex. -/
public noncomputable def oneSubdivisionToCoverSmallChains
    (h : OneSubdivisionMakesCoverSmall X U) :
    (SSet.sd.obj (TopCat.toSSet.obj X)).chainComplex (AddCommGrpCat.of ℤ) ⟶
      CoverSmallIntegralSingularChainComplex X U :=
  subdivisionLastVertexLiftChainMap (coverSmallSingularSubcomplex X U) h

/-- The cover-small lift recovers the last-vertex chain map after inclusion. -/
@[reassoc]
public theorem oneSubdivisionToCoverSmallChains_comp_inclusion
    (h : OneSubdivisionMakesCoverSmall X U) :
    oneSubdivisionToCoverSmallChains X U h ≫
        coverSmallIntegralSingularChainInclusion X U =
      subdivisionLastVertexChainMap (TopCat.toSSet.obj X) :=
  subdivisionLastVertexLiftChainMap_comp_inclusion
    (coverSmallSingularSubcomplex X U) h

/-- A cover containing the whole space satisfies one-subdivision smallness trivially. -/
public theorem oneSubdivisionMakesCoverSmall_of_member_eq_univ
    (j : i) (hj : U j = Set.univ) :
    OneSubdivisionMakesCoverSmall X U := by
  rw [OneSubdivisionMakesCoverSmall,
    coverSmallSingularSubcomplex_eq_top_of_member_eq_univ X U j hj]
  exact le_top

end CoverSmallSubdivision

end AlgebraicTopology.Singular
