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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCohomology
public import FormalConjecturesForMathlib.Mathlib.Algebra.Category.Grp.Basic
public import FormalConjecturesForMathlib.Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# The relative singular-chain sheaf complex

This file constructs the presheaf of relative singular chain complexes
`U ↦ C_*(X, X ∖ U; R)`. For `V ⊆ U`, restriction is the actual relative chain map induced by
the identity map of `X` and the inclusion `X ∖ U ⊆ X ∖ V`. Degreewise sheafification gives a
complex of additive sheaves, then the grading embedding `n ↦ -n` gives a cochain complex
indexed by the integers. All complexes, restrictions, and sheafification maps are constructed;
none are supplied as data.

The conceptual model is the sheafification of relative singular chains described in
Baumann--Kamnitzer--Knutson, *The Mirković--Vilonen basis and Duistermaat--Heckman measures*,
§5.1, p. 24, <https://irma.math.unistra.fr/~baumann/mvbasis.pdf>. No external code is copied.
The sheafification implementation follows the existing `SingularCochainSheaf` module.

This is a concrete candidate for the dualizing complex, not a proof of its dualizing property.
No identification with exceptional pullback, no orientation quasi-isomorphism, and no
identification of its hypercohomology with intrinsic Borel--Moore homology is asserted here.
In particular, stalkwise local homology and the orientation theorem remain separate tasks.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The contravariant functor sending an open set `U` to the pair `(X, X ∖ U)`. -/
def openComplementPairFunctor : (Opens X)ᵒᵖ ⥤ TopPair.{u} where
  obj U := TopPair.ofSubset (U.unop : Set X)ᶜ
  map i := supportInclusionPairMap X (leOfHom i.unop)
  map_id U := supportInclusionPairMap_rfl X (U.unop : Set X)
  map_comp i j :=
    supportInclusionPairMap_trans X (leOfHom j.unop) (leOfHom i.unop)

/-- The actual relative singular-chain complex, contravariantly in the open support. -/
def openRelativeSingularChainComplexFunctor :
    (Opens X)ᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  openComplementPairFunctor X ⋙ relativeChainFunctor R

/-- Relative chains of `(X, X ∖ U)` in degree `n`, forgetting only the scalar structure. -/
def singularChainPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{u} X :=
  openRelativeSingularChainComplexFunctor R X ⋙
    HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n ⋙
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The restriction map is induced by the inclusion of complements, not chosen arbitrarily. -/
@[simp] lemma singularChainPresheaf_map {U V : Opens X} (i : V ⟶ U) (n : ℕ) :
    (singularChainPresheaf R X n).map i.op =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (((relativeChainFunctor R).map
          (supportInclusionPairMap X (leOfHom i))).f n) :=
  rfl

/-- The singular boundary in the relative-chain presheaves. -/
def singularChainBoundary (n : ℕ) :
    singularChainPresheaf R X (n + 1) ⟶ singularChainPresheaf R X n where
  app U := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
    (((openRelativeSingularChainComplexFunctor R X).obj U).d (n + 1) n)
  naturality {U V} i := by
    exact congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
      (((openRelativeSingularChainComplexFunctor R X).map i).comm (n + 1) n)

/-- Restriction commutes with the relative singular boundary. -/
@[reassoc] lemma singularChainBoundary_naturality {U V : Opens X}
    (i : V ⟶ U) (n : ℕ) :
    (singularChainPresheaf R X (n + 1)).map i.op ≫
        (singularChainBoundary R X n).app (.op V) =
      (singularChainBoundary R X n).app (.op U) ≫
        (singularChainPresheaf R X n).map i.op :=
  (singularChainBoundary R X n).naturality i.op

/-- Consecutive relative singular boundaries compose to zero. -/
lemma singularChainBoundary_comp (n : ℕ) :
    singularChainBoundary R X (n + 1) ≫ singularChainBoundary R X n = 0 :=
  NatTrans.ext (funext fun U ↦ congrArg ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map)
    (((openRelativeSingularChainComplexFunctor R X).obj U).d_comp_d (n + 2) (n + 1) n))

/-- The relative singular-chain complex as a complex of additive presheaves. -/
def singularChainPresheafComplex : ChainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℕ :=
  ChainComplex.of (singularChainPresheaf R X) (singularChainBoundary R X)
    (singularChainBoundary_comp R X)

@[simp] lemma singularChainPresheafComplex_d (n : ℕ) :
    (singularChainPresheafComplex R X).d (n + 1) n = singularChainBoundary R X n := by
  simp [singularChainPresheafComplex]

/-- The sheaf of relative singular chains in degree `n`. -/
def singularChainSheaf (n : ℕ) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (singularChainPresheaf R X n)

/-- The sheafified relative singular boundary. -/
def singularChainSheafBoundary (n : ℕ) :
    singularChainSheaf R X (n + 1) ⟶ singularChainSheaf R X n :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (singularChainBoundary R X n)

/-- Degreewise sheafification of the actual relative singular-chain complex. -/
def singularChainSheafComplex : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R X)

@[simp] lemma singularChainSheafComplex_d (n : ℕ) :
    (singularChainSheafComplex R X).d (n + 1) n = singularChainSheafBoundary R X n := by
  change (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((singularChainPresheafComplex R X).d (n + 1) n) = _
  rw [singularChainPresheafComplex_d]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise sheafification unit, as an actual chain map. -/
def singularChainSheafificationUnit :
    singularChainPresheafComplex R X ⟶
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X) where
  f n := toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf R X n)
  comm' i j hij := by
    obtain rfl := hij
    rw [Functor.mapHomologicalComplex_obj_d, singularChainPresheafComplex_d,
      singularChainSheafComplex_d]
    dsimp [singularChainSheafBoundary, singularChainSheaf]
    exact (toSheafify_naturality (Opens.grothendieckTopology X)
      (singularChainBoundary R X j)).symm

/-- Sheafification does not change the stalk of the relative-chain presheaf in any degree. -/
instance singularChainSheafificationUnit_stalk_isIso (x : X) (n : ℕ) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((singularChainSheafificationUnit R X).f n)) :=
  TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (singularChainPresheaf R X n)

/-- The chain-complex-level identification of stalks before and after sheafification.
This is not yet an identification with the local relative homology at `x`. -/
def singularChainSheafificationStalkIso (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex R X) ≅
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex R X)) := by
  let f := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (singularChainSheafificationUnit R X)
  have : ∀ n, IsIso (f.f n) := fun n ↦
    singularChainSheafificationUnit_stalk_isIso R X x n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

/-- The sheafified relative singular-chain model with the cohomological grading convention:
homological degree `n` occupies cohomological degree `-n`, and positive degrees are zero. -/
def singularChainSheafCochainComplex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ :=
  (singularChainSheafComplex R X).extend ComplexShape.embeddingDownNat

/-- Degree `-n` of the integer-graded model is the sheaf of relative `n`-chains. -/
def singularChainSheafCochainComplexXIso (n : ℕ) :
    (singularChainSheafCochainComplex R X).X (-(n : ℤ)) ≅ singularChainSheaf R X n :=
  (singularChainSheafComplex R X).extendXIso ComplexShape.embeddingDownNat rfl

set_option backward.isDefEq.respectTransparency false in
/-- The cohomological differential from degree `-(n+1)` to `-n` is exactly the sheafified
relative singular boundary, transported through the grading isomorphisms. -/
lemma singularChainSheafCochainComplex_d (n : ℕ) :
    (singularChainSheafCochainComplex R X).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (singularChainSheafCochainComplexXIso R X (n + 1)).hom ≫
        singularChainSheafBoundary R X n ≫
          (singularChainSheafCochainComplexXIso R X n).inv := by
  simpa only [singularChainSheafCochainComplex, singularChainSheafCochainComplexXIso,
    singularChainSheafComplex_d] using
    (singularChainSheafComplex R X).extend_d_eq ComplexShape.embeddingDownNat
      (i := n + 1) (j := n) (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) rfl rfl

/-- The constructed integer-graded chain sheaf has no terms in positive degrees. -/
instance singularChainSheafCochainComplex_isStrictlyLE :
    (singularChainSheafCochainComplex R X).IsStrictlyLE 0 := by
  unfold singularChainSheafCochainComplex
  infer_instance

end AlgebraicTopology.Singular
