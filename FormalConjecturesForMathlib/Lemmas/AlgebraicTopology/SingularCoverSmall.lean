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

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Small singular chains for excision

This file builds the first chain-level layer of the singular excision argument.  Given a family
of subsets of a space, the small singular subcomplex consists of the singular simplices which
factor through one member of the family.  Its chain complex maps canonically and monomorphically
to the full singular chain complex, and every cover-member chain map factors through it.

The classical subdivision theorem says that, for an open cover, this inclusion is a chain-homotopy
equivalence.  The definitions below state that next step using mathlib's actual `HomotopyEquiv`
API and prove its full homological consequence.  Mathlib's current simplicial subdivision functor
does not yet provide a last-vertex map, a subdivision chain map, or its chain homotopy to the
identity, so that theorem cannot yet be constructed from library primitives.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology.Singular

/-- Integral singular chains of a categorical topological space. -/
abbrev IntegralSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X

/-- The singular-chain map induced by a continuous map. -/
noncomputable def integralSingularChainMapObj {X Y : TopCat} (i : X ⟶ Y) :
    IntegralSingularChainComplexObj X ⟶ IntegralSingularChainComplexObj Y :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map i

section SmallChains

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- The categorical inclusion of a topological subspace. -/
public noncomputable def topologicalSubsetInclusion (s : Set X) :
    TopCat.of s ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Singular simplices which factor through one member of `U`. -/
public noncomputable def coverSmallSingularSubcomplex :
    (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ j, SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))

public theorem mem_coverSmallSingularSubcomplex_iff
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ j, x ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))).obj n := by
  simp [coverSmallSingularSubcomplex]

/-- Membership means exactly that the singular simplex is the image of a simplex in one cover
member. -/
public theorem mem_coverSmallSingularSubcomplex_iff_exists_preimage
    {n : SimplexCategoryᵒᵖ} (x : (TopCat.toSSet.obj X).obj n) :
    x ∈ (coverSmallSingularSubcomplex X U).obj n ↔
      ∃ (j : ι) (y : (TopCat.toSSet.obj (TopCat.of (U j))).obj n),
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))).app n y = x := by
  simp [mem_coverSmallSingularSubcomplex_iff, Subfunctor.range_obj]

/-- Integral chains on the cover-small singular simplicial set. -/
public noncomputable abbrev CoverSmallIntegralSingularChainComplex :
    ChainComplex AddCommGrpCat ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (AddCommGrpCat.of ℤ)

/-- Inclusion of cover-small integral singular chains into all integral singular chains. -/
public noncomputable def coverSmallIntegralSingularChainInclusion :
    CoverSmallIntegralSingularChainComplex X U ⟶ IntegralSingularChainComplexObj X :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (AddCommGrpCat.of ℤ)

instance coverSmallIntegralSingularChainInclusion_mono :
    Mono (coverSmallIntegralSingularChainInclusion X U) := by
  dsimp [coverSmallIntegralSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The singular set of each cover member factors through the small singular subcomplex. -/
public noncomputable def coverMemberToSmallSingularSet (j : ι) :
    TopCat.toSSet.obj (TopCat.of (U j)) ⟶ coverSmallSingularSubcomplex X U :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
    ((le_iSup (fun k ↦ SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j))

@[reassoc (attr := simp)]
public theorem coverMemberToSmallSingularSet_comp_inclusion (j : ι) :
    coverMemberToSmallSingularSet X U j ≫ (coverSmallSingularSubcomplex X U).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion X (U j)) :=
  SSet.Subcomplex.lift_ι _ _

/-- The chain map from a cover member into the small singular chains. -/
public noncomputable def coverMemberToSmallIntegralSingularChains (j : ι) :
    IntegralSingularChainComplexObj (TopCat.of (U j)) ⟶
      CoverSmallIntegralSingularChainComplex X U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet X U j) (AddCommGrpCat.of ℤ)

/-- Chains from a cover member factor coherently through the small-chain inclusion. -/
@[reassoc]
public theorem coverMemberToSmallIntegralSingularChains_comp_inclusion (j : ι) :
    coverMemberToSmallIntegralSingularChains X U j ≫
        coverSmallIntegralSingularChainInclusion X U =
      integralSingularChainMapObj (topologicalSubsetInclusion X (U j)) := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverMemberToSmallSingularSet X U j) ≫
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (coverSmallSingularSubcomplex X U).ι =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U j)))
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]

/-- A subspace equal to the whole space is homeomorphic to the ambient space by its inclusion. -/
public noncomputable def topologicalSubsetHomeomorphOfEqUniv
    (s : Set X) (hs : s = Set.univ) : s ≃ₜ X :=
  (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ X)

/-- The subspace inclusion is an isomorphism when the subset is all of `X`. -/
public theorem topologicalSubsetInclusion_isIso_of_eq_univ
    (s : Set X) (hs : s = Set.univ) :
    IsIso (topologicalSubsetInclusion X s) := by
  change IsIso (TopCat.isoOfHomeo
    (X := TopCat.of s) (Y := X) (topologicalSubsetHomeomorphOfEqUniv X s hs)).hom
  infer_instance

/-- If one cover member is the whole space, every singular simplex is already small. -/
public theorem coverSmallSingularSubcomplex_eq_top_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    coverSmallSingularSubcomplex X U = ⊤ := by
  let := topologicalSubsetInclusion_isIso_of_eq_univ X (U j) hj
  have hrange : SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U j))) = ⊤ :=
    SSet.Subcomplex.range_eq_top _
  exact top_unique (hrange ▸ le_iSup (fun k ↦ SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubsetInclusion X (U k)))) j)

/-- For a cover containing the whole space, the small-chain inclusion is an isomorphism. -/
public theorem coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    IsIso (coverSmallIntegralSingularChainInclusion X U) := by
  let htop := coverSmallSingularSubcomplex_eq_top_of_member_eq_univ X U j hj
  let e : (coverSmallSingularSubcomplex X U : SSet) ≅ TopCat.toSSet.obj X :=
    SSet.Subcomplex.eqToIso htop ≪≫ SSet.Subcomplex.topIso _
  have he : e.hom = (coverSmallSingularSubcomplex X U).ι := by
    dsimp [e]
    exact SSet.Subcomplex.homOfLE_ι htop.le
  change IsIso (((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).map (coverSmallSingularSubcomplex X U).ι)
  rw [← he]
  infer_instance

/-- The small-chain approximation theorem holds directly for a cover containing the whole
space, without subdivision. -/
public theorem coverSmallChainApproximation_of_member_eq_univ
    (j : ι) (hj : U j = Set.univ) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (coverSmallIntegralSingularChainInclusion X U) := by
  let := coverSmallIntegralSingularChainInclusion_isIso_of_member_eq_univ X U j hj
  exact HomologicalComplex.homotopyEquivalences.of_isIso _

end SmallChains


end AlgebraicTopology.Singular
