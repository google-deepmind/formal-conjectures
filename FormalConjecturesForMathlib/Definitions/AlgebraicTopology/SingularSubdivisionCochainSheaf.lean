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

public import FormalConjecturesForMathlib.Mathlib.Algebra.Homology.KernelAcyclic
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.FlasqueAcyclic
public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularCochainCohomology
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCochainSheafFlasque
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularExcisionField
public import FormalConjecturesForMathlib.Mathlib.Topology.ChartedSpaceParacompact

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.ShrinkingLemma

/-!
# Global and locally defined singular cochains

This file proves the global comparison used in the singular-to-sheaf cohomology theorem.
Ordinary singular cochains agree with cochains on the top open subset. Subdivision kills the
locally zero kernel of the first plus construction. On paracompact Hausdorff spaces, a locally
finite closed refinement also makes the second plus map surjective on global sections. The
double-plus complex is then identified with Mathlib's chosen degreewise sheafification.

The first plus construction is only an intermediate separated presheaf; no sheaf claim is made
for it. The final comparison uses the double-plus sheaf and the canonical isomorphism to the
chosen singular-cochain sheaf complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

/-- The domains of a covering sieve, regarded as open subsets of the covered open set. -/
def coveringSieveOpenFamilyOn (X : TopCat.{u}) {U : Opens X}
    (S : (Opens.grothendieckTopology X).Cover U) : S.Arrow → Set U :=
  fun I ↦ Subtype.val ⁻¹' (I.Y : Set X)

private lemma coveringSieveOpenFamilyOn_isOpen (X : TopCat.{u}) {U : Opens X}
    (S : (Opens.grothendieckTopology X).Cover U) (I : S.Arrow) :
    IsOpen (coveringSieveOpenFamilyOn X S I) :=
  I.Y.isOpen.preimage continuous_subtype_val

/-- The domains of a covering sieve cover the covered open set. -/
private lemma coveringSieveOpenFamilyOn_iUnion (X : TopCat.{u}) {U : Opens X}
    (S : (Opens.grothendieckTopology X).Cover U) :
    ⋃ I, coveringSieveOpenFamilyOn X S I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨V, f, hf, hx⟩ :=
    ((Opens.mem_grothendieckTopology X).mp S.2) x.1 x.2
  exact Set.mem_iUnion.mpr
    ⟨GrothendieckTopology.Cover.Arrow.mk V f hf, hx⟩

/-- On a paracompact Hausdorff open set, a covering sieve admits an open refinement whose
closures are locally finite and remain subordinate to the original sieve members. -/
private theorem exists_coveringSieve_locallyFinite_closedRefinement
    (X : TopCat.{u}) {U : Opens X} [ParacompactSpace U] [T2Space U]
    (S : (Opens.grothendieckTopology X).Cover U) :
    ∃ W : S.Arrow → Set U,
      (∀ I, IsOpen (W I)) ∧ ⋃ I, W I = Set.univ ∧
        LocallyFinite (fun I ↦ closure (W I)) ∧
          ∀ I, closure (W I) ⊆ coveringSieveOpenFamilyOn X S I := by
  obtain ⟨V, hVopen, hVcover, hVfinite, hVsub⟩ := precise_refinement
    (coveringSieveOpenFamilyOn X S)
    (coveringSieveOpenFamilyOn_isOpen X S)
    (coveringSieveOpenFamilyOn_iUnion X S)
  let : NormalSpace U := inferInstance
  obtain ⟨W, hWcover, hWopen, hWsub⟩ :=
    exists_iUnion_eq_closure_subset hVopen hVfinite.point_finite hVcover
  refine ⟨W, hWopen, hWcover, ?_, fun I ↦ (hWsub I).trans (hVsub I)⟩
  exact (hVfinite.subset fun I ↦ subset_closure.trans (hWsub I)).closure

/-- Lift a singular simplex through an inclusion of open subsets, provided all of its values lie
in the smaller open subset. -/
noncomputable def openSimplexLift {X : TopCat.{u}} {U V : Opens X} (_i : V ⟶ U) (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    OpenSimplex X (.op V) n := by
  let m := Opposite.op (SimplexCategory.mk n)
  let fs := (TopCat.of U).toSSetObjEquiv m s
  let f : C(stdSimplex ℝ (Fin (n + 1)), TopCat.of V) :=
    ⟨fun z ↦ ⟨((fs z : U) : X), h z⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp fs.continuous) _⟩
  exact (TopCat.of V).toSSetObjEquiv m |>.symm f

@[simp]
lemma openSimplexMap_openSimplexLift {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U) (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    openSimplexMap X i.op n (openSimplexLift i n s h) = s := by
  apply (TopCat.of U).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n)) |>.injective
  rfl

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- The ordinary singular chain complex of `X` with coefficients in `R`. -/
abbrev SingularChainComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X

/-- The singular chain complex of the top open subset of `X`. -/
abbrev TopOpenSingularChainComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  (openSingularChainComplexFunctor R X).obj ⊤

/-- The inclusion of the top open subset into `X` identifies their singular chain complexes. -/
noncomputable def topOpenSingularChainComplexIso :
    TopOpenSingularChainComplex R X ≅ SingularChainComplex R X :=
  ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).mapIso
    (Opens.inclusionTopIso X)

/-- Ordinary singular cochains and top-open singular cochains are isomorphic as cochain
complexes. -/
noncomputable def singularCochainComplexIsoTopOpen :
    (SingularChainComplex R X).linearDualCochainComplex ≅
      (TopOpenSingularChainComplex R X).linearDualCochainComplex :=
  HomologicalComplex.linearDualIso (topOpenSingularChainComplexIso R X)

/-- Ordinary singular cochain cohomology is canonically linearly equivalent to the cohomology of
cochains on the top open subset. -/
noncomputable def cochainCohomologyEquivTopOpen (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R]
      ((TopOpenSingularChainComplex R X).sc n).linearDual.homology :=
  HomologicalComplex.HomotopyEquiv.linearDualCohomologyEquiv
    (HomotopyEquiv.ofIso (topOpenSingularChainComplexIso R X)) n

/-- The singular-cochain presheaf complex evaluated on the top open subset. -/
def globalRawSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex R X)

/-- Top-open singular cochains, with their scalar structure forgotten. -/
def topOpenForgottenSingularCochainComplex : CochainComplex AddCommGrpCat ℕ :=
  ((forget₂ (ModuleCat.{u} R) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj
      (TopOpenSingularChainComplex R X).linearDualCochainComplex

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the cochain presheaf and forgetting the scalar structure on top-open cochains
have the same underlying additive groups. -/
def globalRawSingularCochainAddEquiv (n : ℕ) :
    (globalRawSingularCochainComplex R X).X n ≃+
      (topOpenForgottenSingularCochainComplex R X).X n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The degreewise additive-group isomorphism between the two presentations of top-open
cochains. -/
def globalRawSingularCochainXIso (n : ℕ) :
    (globalRawSingularCochainComplex R X).X n ≅
      (topOpenForgottenSingularCochainComplex R X).X n :=
  (globalRawSingularCochainAddEquiv R X n).toAddCommGrpIso

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the raw cochain presheaf on the top open agrees, as a complex of additive groups,
with forgetting the scalar structure on the top-open linear-dual complex. -/
def globalRawSingularCochainComplexIso :
    globalRawSingularCochainComplex R X ≅
      topOpenForgottenSingularCochainComplex R X :=
  HomologicalComplex.Hom.isoOfComponents
    (globalRawSingularCochainXIso R X) (by
      intro i j hij
      obtain rfl := hij
      ext x
      dsimp only [globalRawSingularCochainComplex,
        topOpenForgottenSingularCochainComplex]
      rw [Functor.mapHomologicalComplex_obj_d,
        Functor.mapHomologicalComplex_obj_d,
        singularCochainPresheafComplex_d,
        HomologicalComplex.linearDualCochainComplex_d]
      dsimp [globalRawSingularCochainXIso,
        globalRawSingularCochainAddEquiv,
        TopOpenSingularChainComplex, singularCochainCoboundary]
      rfl)

@[simp]
lemma globalRawSingularCochainComplexIso_hom_f_apply (n : ℕ)
    (x : (globalRawSingularCochainComplex R X).X n) :
    (globalRawSingularCochainComplexIso R X).hom.f n x = x :=
  rfl

/-- The singular-cochain presheaf complex after applying the first plus construction degreewise.
This is a complex of presheaves, not a complex of sheaves. -/
def singularCochainPlusPresheafComplex :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  ((Opens.grothendieckTopology X).plusFunctor AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ) |>.obj (singularCochainPresheafComplex R X)

/-- The degreewise first-plus unit on the singular-cochain presheaf complex. -/
def singularCochainToPlusPresheafComplex :
    singularCochainPresheafComplex R X ⟶ singularCochainPlusPresheafComplex R X :=
  (NatTrans.mapHomologicalComplex
    ((Opens.grothendieckTopology X).toPlusNatTrans AddCommGrpCat)
    (ComplexShape.up ℕ)).app (singularCochainPresheafComplex R X)

@[simp]
lemma singularCochainToPlusPresheafComplex_f (n : ℕ) :
    (singularCochainToPlusPresheafComplex R X).f n =
      (Opens.grothendieckTopology X).toPlus (singularCochainPresheaf R X n) :=
  rfl

/-- The singular-cochain presheaf complex after applying the plus construction twice
degreewise. Every term of this complex is a sheaf. -/
def singularCochainPlusPlusPresheafComplex :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  (((Opens.grothendieckTopology X).sheafification
    AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (singularCochainPresheafComplex R X)

/-- The degreewise second-plus unit on the singular-cochain complex. -/
def singularCochainPlusToPlusPlusPresheafComplex :
    singularCochainPlusPresheafComplex R X ⟶
      singularCochainPlusPlusPresheafComplex R X :=
  (NatTrans.mapHomologicalComplex
    (Functor.whiskerLeft
      ((Opens.grothendieckTopology X).plusFunctor AddCommGrpCat)
      ((Opens.grothendieckTopology X).toPlusNatTrans AddCommGrpCat))
    (ComplexShape.up ℕ)).app (singularCochainPresheafComplex R X)

@[simp]
lemma singularCochainPlusToPlusPlusPresheafComplex_f (n : ℕ) :
    (singularCochainPlusToPlusPlusPresheafComplex R X).f n =
      (Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n)) :=
  rfl

/-- The degreewise double-plus comparison from raw singular cochains. -/
def singularCochainToPlusPlusPresheafComplex :
    singularCochainPresheafComplex R X ⟶
      singularCochainPlusPlusPresheafComplex R X :=
  singularCochainToPlusPresheafComplex R X ≫
    singularCochainPlusToPlusPlusPresheafComplex R X

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma singularCochainToPlusPlusPresheafComplex_f (n : ℕ) :
    (singularCochainToPlusPlusPresheafComplex R X).f n =
      (Opens.grothendieckTopology X).toSheafify
        (singularCochainPresheaf R X n) := by
  change (Opens.grothendieckTopology X).toPlus
      (singularCochainPresheaf R X n) ≫
        (Opens.grothendieckTopology X).toPlus
          ((Opens.grothendieckTopology X).plusObj
            (singularCochainPresheaf R X n)) = _
  rw [← (Opens.grothendieckTopology X).plusMap_toPlus
    (singularCochainPresheaf R X n)]
  rfl

/-- The underlying presheaf complex of the chosen degreewise sheafification. -/
def forgottenSingularCochainSheafComplex :
    CochainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  ((TopCat.Sheaf.forget AddCommGrpCat X).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (singularCochainSheafComplex R X)

/-- Double-plus sheafification agrees with Mathlib's chosen sheafification, compatibly with the
singular coboundary. -/
def singularCochainPlusPlusPresheafComplexIsoSheafComplex :
    singularCochainPlusPlusPresheafComplex R X ≅
      forgottenSingularCochainSheafComplex R X :=
  (NatIso.mapHomologicalComplex
    (plusPlusFunctorIsoSheafification
      (Opens.grothendieckTopology X) AddCommGrpCat)
    (ComplexShape.up ℕ)).app (singularCochainPresheafComplex R X)

/-- Flasqueness descends along a pointwise epimorphism of additive presheaves. -/
lemma presheaf_isFlasque_of_epi
    {P Q : TopCat.Presheaf AddCommGrpCat X} (f : P ⟶ Q)
    [P.IsFlasque] [∀ U, Epi (f.app U)] : Q.IsFlasque where
  epi {U V} i := by
    have hcomp : Epi (f.app U ≫ Q.map i) := by
      rw [← f.naturality i]
      infer_instance
    exact CategoryTheory.epi_of_epi (f.app U) (Q.map i)

/-- Every degree of the first-plus singular-cochain complex is a flasque presheaf. -/
instance singularCochainPlusPresheafComplex_isFlasque (n : ℕ) :
    TopCat.Presheaf.IsFlasque ((singularCochainPlusPresheafComplex R X).X n) := by
  change TopCat.Presheaf.IsFlasque
    ((Opens.grothendieckTopology X).plusObj
      (singularCochainPresheaf R X n))
  infer_instance

/-- Evaluation of the first-plus singular-cochain complex on the top open subset. -/
def globalSingularCochainPlusComplex : CochainComplex AddCommGrpCat ℕ :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ) |>.obj (singularCochainPlusPresheafComplex R X)

/-- Evaluation on the top open subset of the degreewise first-plus comparison. -/
def topOpenToGlobalSingularCochainPlusComplex :
    globalRawSingularCochainComplex R X ⟶
        globalSingularCochainPlusComplex R X :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainToPlusPresheafComplex R X)

/-- Evaluation of the double-plus singular-cochain complex on the top open subset. -/
def globalSingularCochainPlusPlusComplex : CochainComplex AddCommGrpCat ℕ :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ) |>.obj (singularCochainPlusPlusPresheafComplex R X)

/-- Global sections of the chosen singular-cochain sheaf complex. -/
def globalSingularCochainSheafComplex : CochainComplex AddCommGrpCat ℕ :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ) |>.obj (forgottenSingularCochainSheafComplex R X)

/-- The double-plus model and the chosen singular-cochain sheaf complex have isomorphic global
section complexes. -/
def globalSingularCochainPlusPlusComplexIsoSheafComplex :
    globalSingularCochainPlusPlusComplex R X ≅
      globalSingularCochainSheafComplex R X :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).mapIso
      (singularCochainPlusPlusPresheafComplexIsoSheafComplex R X)

/-- Evaluation on the top open subset of the degreewise second-plus comparison. -/
def globalSingularCochainPlusToPlusPlusComplex :
    globalSingularCochainPlusComplex R X ⟶
      globalSingularCochainPlusPlusComplex R X :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (singularCochainPlusToPlusPlusPresheafComplex R X)

/-- Evaluation on the top open subset of the degreewise double-plus comparison. -/
def topOpenToGlobalSingularCochainPlusPlusComplex :
    globalRawSingularCochainComplex R X ⟶
      globalSingularCochainPlusPlusComplex R X :=
  topOpenToGlobalSingularCochainPlusComplex R X ≫
    globalSingularCochainPlusToPlusPlusComplex R X

/-- The comparison from ordinary singular cochains to global sections of the chosen
singular-cochain sheaf complex. -/
def topOpenToGlobalSingularCochainSheafComplex :
    globalRawSingularCochainComplex R X ⟶
      globalSingularCochainSheafComplex R X :=
  topOpenToGlobalSingularCochainPlusPlusComplex R X ≫
    (globalSingularCochainPlusPlusComplexIsoSheafComplex R X).hom

/-- Every global section of the first-plus term is represented by an ordinary cochain. -/
lemma topOpenToGlobalSingularCochainPlusComplex_surjective (n : ℕ) :
    Function.Surjective
      ((topOpenToGlobalSingularCochainPlusComplex R X).f n) :=
  singularCochain_toPlus_exists_rep R X ⊤ n

/-- The map from top-open cochains to global first-plus cochains is degreewise an epimorphism. -/
instance topOpenToGlobalSingularCochainPlusComplex_epi_f (n : ℕ) :
    Epi ((topOpenToGlobalSingularCochainPlusComplex R X).f n) := by
  rw [AddCommGrpCat.epi_iff_surjective]
  exact topOpenToGlobalSingularCochainPlusComplex_surjective R X n

set_option backward.isDefEq.respectTransparency false in
/-- A singular cochain maps to zero in the first plus construction exactly when it vanishes
after restriction along every arrow of some covering sieve. -/
lemma singularCochain_toPlus_eq_zero_iff (V : Opens X) (n : ℕ)
    (φ : OpenCochains R X (.op V) n) :
    ((Opens.grothendieckTopology X).toPlus
        (singularCochainPresheaf R X n)).app (.op V) φ = 0 ↔
      ∃ S : (Opens.grothendieckTopology X).Cover V,
        ∀ I : S.Arrow,
          (singularCochainPresheaf R X n).map I.f.op φ = 0 := by
  let J := Opens.grothendieckTopology X
  let P := singularCochainPresheaf R X n
  change (J.toPlus P).app (.op V) φ = 0 ↔ _
  rw [← map_zero (ConcreteCategory.hom ((J.toPlus P).app (.op V)))]
  constructor
  · intro h
    simp only [GrothendieckTopology.Plus.toPlus_eq_mk] at h
    rw [GrothendieckTopology.Plus.eq_mk_iff_exists] at h
    obtain ⟨S, h₁, h₂, hS⟩ := h
    refine ⟨S, fun I ↦ ?_⟩
    apply_fun fun e ↦ e I at hS
    simpa [Meq.refine, Meq.mk, P] using hS
  · rintro ⟨S, hS⟩
    simp only [GrothendieckTopology.Plus.toPlus_eq_mk]
    rw [GrothendieckTopology.Plus.eq_mk_iff_exists]
    refine ⟨S, homOfLE le_top, homOfLE le_top, ?_⟩
    ext I
    simpa [Meq.refine, Meq.mk, P] using hS I

set_option backward.isDefEq.respectTransparency false in
/-- Raw representatives of a matching family of first-plus singular cochains agree on some
neighborhood of every point of a pairwise overlap. -/
private lemma exists_open_eq_of_plus_matchingFamily
    {U : Opens X} (S : (Opens.grothendieckTopology X).Cover U) (n : ℕ)
    (s : Meq ((Opens.grothendieckTopology X).plusObj
      (singularCochainPresheaf R X n)) S)
    (φ : ∀ I : S.Arrow, OpenCochains R X (.op I.Y) n)
    (hφ : ∀ I : S.Arrow,
      ((Opens.grothendieckTopology X).toPlus
        (singularCochainPresheaf R X n)).app (.op I.Y) (φ I) = s I)
    (I J : S.Arrow) (x : X) (hxI : x ∈ I.Y) (hxJ : x ∈ J.Y) :
    ∃ (V : Opens X) (a : V ⟶ I.Y) (b : V ⟶ J.Y), x ∈ V ∧
      (singularCochainPresheaf R X n).map a.op (φ I) =
        (singularCochainPresheaf R X n).map b.op (φ J) := by
  let eI : I.Y ⊓ J.Y ⟶ I.Y := homOfLE inf_le_left
  let eJ : I.Y ⊓ J.Y ⟶ J.Y := homOfLE inf_le_right
  let rel : S.Relation := GrothendieckTopology.Cover.Relation.mk'
    { Z := I.Y ⊓ J.Y
      g₁ := eI
      g₂ := eJ }
  have hplus := s.condition rel
  change ((Opens.grothendieckTopology X).plusObj
      (singularCochainPresheaf R X n)).map eI.op (s I) =
    ((Opens.grothendieckTopology X).plusObj
      (singularCochainPresheaf R X n)).map eJ.op (s J) at hplus
  let η := (Opens.grothendieckTopology X).toPlus
    (singularCochainPresheaf R X n)
  have hplus' :
      η.app (.op (I.Y ⊓ J.Y))
          ((singularCochainPresheaf R X n).map eI.op (φ I)) =
        η.app (.op (I.Y ⊓ J.Y))
          ((singularCochainPresheaf R X n).map eJ.op (φ J)) := by
    calc
      _ = ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n)).map eI.op
            (η.app (.op I.Y) (φ I)) := by
              simpa only [ConcreteCategory.comp_apply] using
                ConcreteCategory.congr_hom (η.naturality eI.op) (φ I)
      _ = ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n)).map eI.op (s I) := by rw [hφ I]
      _ = ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n)).map eJ.op (s J) := hplus
      _ = ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n)).map eJ.op
            (η.app (.op J.Y) (φ J)) := by rw [hφ J]
      _ = η.app (.op (I.Y ⊓ J.Y))
          ((singularCochainPresheaf R X n).map eJ.op (φ J)) := by
              simpa only [ConcreteCategory.comp_apply] using
                (ConcreteCategory.congr_hom (η.naturality eJ.op) (φ J)).symm
  let δ : OpenCochains R X (.op (I.Y ⊓ J.Y)) n :=
    (singularCochainPresheaf R X n).map eI.op (φ I) -
      (singularCochainPresheaf R X n).map eJ.op (φ J)
  have hδplus :
      ((Opens.grothendieckTopology X).toPlus
        (singularCochainPresheaf R X n)).app (.op (I.Y ⊓ J.Y)) δ = 0 := by
    rw [map_sub, hplus', sub_self]
  obtain ⟨T, hT⟩ :=
    (singularCochain_toPlus_eq_zero_iff R X (I.Y ⊓ J.Y) n δ).mp hδplus
  obtain ⟨V, f, hf, hxV⟩ :=
    ((Opens.mem_grothendieckTopology X).mp T.2) x ⟨hxI, hxJ⟩
  let A : T.Arrow := GrothendieckTopology.Cover.Arrow.mk V f hf
  refine ⟨V, f ≫ eI, f ≫ eJ, hxV, ?_⟩
  have hz := hT A
  change (singularCochainPresheaf R X n).map f.op δ = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  simpa only [δ, Functor.map_comp, op_comp,
    ConcreteCategory.comp_apply] using hz

section RationalCover

variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- The family of open subsets appearing as the domains of the arrows in a covering sieve of the
top open subset. -/
def coveringSieveOpenFamily
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) : S.Arrow → Set Y :=
  fun I ↦ I.Y

/-- Restriction of rational singular cochains to chains subordinate to a family of subsets. -/
def rationalCochainRestrictionToCoverSmall :
    ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℚ ℚ)).linearDualCochainComplex ⟶
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualMap (coverSmallRationalSingularChainInclusion Y U)

/-- The chain map from one member of a family into the cover-small rational chains. -/
def coverMemberToSmallRationalSingularChains (j : κ) :
    (TopCat.toSSet.obj (TopCat.of (U j))).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      CoverSmallRationalSingularChainComplex Y U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet Y U j) (ModuleCat.of ℚ ℚ)

/-- Restriction to cover-small rational chains is surjective in every cochain degree. -/
lemma rationalCochainRestrictionToCoverSmall_surjective (n : ℕ) :
    Function.Surjective ((rationalCochainRestrictionToCoverSmall Y U).f n) := by
  apply LinearMap.dualMap_surjective_of_injective
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)
    (coverSmallRationalSingularChainInclusion Y U)

/-- Restriction to cover-small rational chains is an epimorphism of cochain complexes. -/
instance rationalCochainRestrictionToCoverSmall_epi :
    Epi (rationalCochainRestrictionToCoverSmall Y U) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ by
    rw [ModuleCat.epi_iff_surjective]
    exact rationalCochainRestrictionToCoverSmall_surjective Y U n

/-- An open cover gives a homotopy equivalence from all rational cochains to its cover-small
cochains. -/
def rationalCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℚ ℚ)).linearDualCochainComplex
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualHomotopyEquiv
    (coverSmallRationalChainHomotopyEquiv_of_openCover Y U hUopen hUcover)

/-- The map from top-open cochains to global first-plus cochains is an epimorphism of complexes.
-/
instance topOpenToGlobalSingularCochainPlusComplex_epi :
    Epi (topOpenToGlobalSingularCochainPlusComplex R X) :=
  HomologicalComplex.epi_of_epi_f _ fun _ ↦ inferInstance

/-- Restriction from cochains on the top open subset to chains subordinate to a family of
subsets. -/
def topOpenRationalCochainRestrictionToCoverSmall :
    (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex ⟶
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
  (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
    rationalCochainRestrictionToCoverSmall Y U

instance topOpenRationalCochainRestrictionToCoverSmall_epi :
    Epi (topOpenRationalCochainRestrictionToCoverSmall Y U) := by
  apply HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
  rw [ModuleCat.epi_iff_surjective]
  have h₁ : Function.Surjective
      ((singularCochainComplexIsoTopOpen ℚ Y).inv.f n) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  have h₂ := rationalCochainRestrictionToCoverSmall_surjective Y U n
  intro z
  obtain ⟨y, hy⟩ := h₂ z
  obtain ⟨x, hx⟩ := h₁ y
  refine ⟨x, ?_⟩
  change (rationalCochainRestrictionToCoverSmall Y U).f n
      ((singularCochainComplexIsoTopOpen ℚ Y).inv.f n x) = z
  rw [hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- The cover-small homotopy equivalence, with its source written as cochains on the top open
subset. -/
def topOpenRationalCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
  by
    let e₁ : HomotopyEquiv
        (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
        ((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of ℚ ℚ)).linearDualCochainComplex :=
      HomotopyEquiv.ofIso (singularCochainComplexIsoTopOpen ℚ Y).symm
    exact e₁.trans
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover)

end RationalCover

section HereditarilyParacompact

variable {R : Type u} [Field R] {X : TopCat.{u}}

/-- Regard an open subset of an open subspace as an open subset of the ambient space. -/
def ambientOpen (U : Opens X) (V : Opens U) : Opens X :=
  ⟨Subtype.val '' (V : Set U),
    U.isOpen.isOpenMap_subtype_val (V : Set U) V.isOpen⟩

@[simp]
lemma mem_ambientOpen_iff (U : Opens X) (V : Opens U) (x : U) :
    (x.1 : X) ∈ ambientOpen U V ↔ x ∈ V := by
  change x.1 ∈ Subtype.val '' (V : Set U) ↔ x ∈ V
  refine ⟨fun ⟨y, hy, hxy⟩ ↦ ?_, fun hx ↦ ⟨x, hx, rfl⟩⟩
  have h : y = x := Subtype.ext hxy
  exact show x ∈ (V : Set U) from h ▸ hy

private lemma ambientOpen_le (U : Opens X) (V : Opens U) : ambientOpen U V ≤ U := by
  change Subtype.val '' (V : Set U) ⊆ U
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- The sieve generated by an indexed family of open subsets of a fixed open set. -/
def openFamilySieve {U : Opens X} {I : Type*} (V : I → Opens X)
    (_hV : ∀ i, V i ≤ U) : Sieve U where
  arrows W f := ∃ i, W ≤ V i
  downward_closed := by
    rintro A B f ⟨i, hi⟩ g
    exact ⟨i, g.le.trans hi⟩

/-- A pointwise covering family defines a covering sieve. -/
private lemma openFamilySieve_mem {U : Opens X} {I : Type*} (V : I → Opens X)
    (hV : ∀ i, V i ≤ U) (hcover : ∀ x ∈ U, ∃ i, x ∈ V i) :
    openFamilySieve V hV ∈ Opens.grothendieckTopology X U := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨i, hxi⟩ := hcover x hx
  exact ⟨V i, homOfLE (hV i), ⟨i, le_rfl⟩, hxi⟩

set_option backward.isDefEq.respectTransparency false in
/-- On a paracompact Hausdorff open set, every section of the second plus construction of the
singular-cochain presheaf lifts to the first plus construction.  This is the precise hypothesis
under which the usually quoted flasqueness argument is valid; it is false on arbitrary spaces. -/
theorem singularCochain_plusToPlus_surjective_on
    (U : Opens X) [ParacompactSpace U] [T2Space U] (n : ℕ) :
    Function.Surjective
      (((Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n))).app (.op U)) := by
  classical
  let J := Opens.grothendieckTopology X
  let P := singularCochainPresheaf R X n
  intro y
  obtain ⟨S, s, rfl⟩ := GrothendieckTopology.Plus.exists_rep y
  choose φ hφ using fun I : S.Arrow ↦
    singularCochain_toPlus_exists_rep R X I.Y n (s I)
  obtain ⟨W, hWopen, hWcover, hWfinite, hWsub⟩ :=
    exists_coveringSieve_locallyFinite_closedRefinement X S
  have hWmem (x : U) : ∃ I : S.Arrow, x ∈ W I := by
    have hx : x ∈ ⋃ I, W I := by rw [hWcover]; trivial
    simpa only [Set.mem_iUnion] using hx
  choose b hb using hWmem
  have hbY (x : U) : (x.1 : X) ∈ (b x).Y :=
    hWsub (b x) (subset_closure (hb x))
  have hlocalEq (x : U) (I : S.Arrow) (hxI : x ∈ closure (W I)) :
      ∃ (V : Opens X) (a : V ⟶ (b x).Y) (c : V ⟶ I.Y),
        (x.1 : X) ∈ V ∧
          P.map a.op (φ (b x)) = P.map c.op (φ I) :=
    exists_open_eq_of_plus_matchingFamily R X S n s φ hφ
      (b x) I x.1 (hbY x) (hWsub I hxI)
  let E (x : U) (I : S.Arrow) : Opens X :=
    if h : x ∈ closure (W I) then (hlocalEq x I h).choose else ⊤
  have hE (x : U) (I : S.Arrow) (hxI : x ∈ closure (W I)) :
      ∃ (a : E x I ⟶ (b x).Y) (c : E x I ⟶ I.Y),
        (x.1 : X) ∈ E x I ∧
          P.map a.op (φ (b x)) = P.map c.op (φ I) := by
    rw [show E x I = (hlocalEq x I hxI).choose by simp [E, hxI]]
    exact (hlocalEq x I hxI).choose_spec
  let Nset (x : U) : Set U :=
    W (b x) ∩
      (⋂ I ∈ {I | x ∈ closure (W I)},
        Subtype.val ⁻¹' (E x I : Set X)) ∩
      (⋂ (I : S.Arrow) (_ : x ∉ closure (W I)), (closure (W I))ᶜ)
  have hNset_mem (x : U) : Nset x ∈ nhds x := by
    have hWnhds : W (b x) ∈ nhds x := (hWopen (b x)).mem_nhds (hb x)
    have hfinite : {I | x ∈ closure (W I)}.Finite :=
      hWfinite.point_finite x
    have hEqnhds :
        (⋂ I ∈ {I | x ∈ closure (W I)},
          Subtype.val ⁻¹' (E x I : Set X)) ∈ nhds x := by
      refine (Filter.biInter_mem hfinite).2 (fun I hIx ↦ ?_)
      exact ((E x I).isOpen.preimage continuous_subtype_val).mem_nhds
        ((hE x I hIx).choose_spec.choose_spec.1)
    have hAvoid :
        (⋂ (I : S.Arrow) (_ : x ∉ closure (W I)), (closure (W I))ᶜ) ∈ nhds x :=
      hWfinite.iInter_compl_mem_nhds (fun I ↦ isClosed_closure) x
    exact Filter.inter_mem (Filter.inter_mem hWnhds hEqnhds) hAvoid
  let Nsub (x : U) : Opens U :=
    ⟨interior (Nset x), isOpen_interior⟩
  have hxNsub (x : U) : x ∈ Nsub x :=
    mem_interior_iff_mem_nhds.mpr (hNset_mem x)
  let N (x : U) : Opens X := ambientOpen U (Nsub x)
  have hxN (x : U) : (x.1 : X) ∈ N x :=
    (mem_ambientOpen_iff U (Nsub x) x).2 (hxNsub x)
  have hN_le_U (x : U) : N x ≤ U := ambientOpen_le U (Nsub x)
  have hNsub_Nset (x : U) : (Nsub x : Set U) ⊆ Nset x :=
    interior_subset
  have hN_le_component (x : U) : N x ≤ (b x).Y := by
    intro z hz
    obtain ⟨zU, hzN, rfl⟩ := hz
    have hzW : zU ∈ W (b x) := (hNsub_Nset x hzN).1.1
    exact hWsub (b x) (subset_closure hzW)
  have hN_le_E (x : U) (I : S.Arrow) (hxI : x ∈ closure (W I)) :
      N x ≤ E x I := by
    intro z hz
    obtain ⟨zU, hzN, rfl⟩ := hz
    have hzEq := (hNsub_Nset x hzN).1.2
    exact Set.mem_iInter₂.mp hzEq I hxI
  have hN_meets_W (x : U) (I : S.Arrow)
      (hmeet : ((Nsub x : Set U) ∩ W I).Nonempty) :
      x ∈ closure (W I) := by
    by_contra hxI
    obtain ⟨z, hzN, hzW⟩ := hmeet
    have hzAvoid := (hNsub_Nset x hzN).2
    have hznot : z ∉ closure (W I) := Set.mem_iInter₂.mp hzAvoid I hxI
    exact hznot (subset_closure hzW)
  let iNU (x : U) : N x ⟶ U := homOfLE (hN_le_U x)
  let iNB (x : U) : N x ⟶ (b x).Y := homOfLE (hN_le_component x)
  let φN (x : U) : OpenCochains R X (.op (N x)) n :=
    P.map (iNB x).op (φ (b x))
  have hφN (x z : U) :
      P.map (homOfLE (inf_le_left : N x ⊓ N z ≤ N x)).op (φN x) =
        P.map (homOfLE (inf_le_right : N x ⊓ N z ≤ N z)).op (φN z) := by
    apply (singularCochainEquivSimplexFunction R X (.op (N x ⊓ N z)) n).injective
    ext r
    let q : ↑(N x ⊓ N z) :=
      (TopCat.of ↑(N x ⊓ N z)).toSSetObjEquiv
        (Opposite.op (SimplexCategory.mk n)) r (Classical.arbitrary _)
    have hmeet : ((Nsub x : Set U) ∩ W (b z)).Nonempty := by
      let qU : U := ⟨q.1, hN_le_U x q.2.1⟩
      refine ⟨qU, ?_, ?_⟩
      · exact (mem_ambientOpen_iff U (Nsub x) qU).1 q.2.1
      · exact (hNsub_Nset z
          ((mem_ambientOpen_iff U (Nsub z) qU).1 q.2.2)).1.1
    have hxz : x ∈ closure (W (b z)) := hN_meets_W x (b z) hmeet
    obtain ⟨a, c, -, heq⟩ := hE x (b z) hxz
    let l : N x ⊓ N z ⟶ N x := homOfLE inf_le_left
    let rgt : N x ⊓ N z ⟶ N z := homOfLE inf_le_right
    let k : N x ⊓ N z ⟶ E x (b z) :=
      homOfLE (inf_le_left.trans (hN_le_E x (b z) hxz))
    have hleft : l ≫ iNB x = k ≫ a := Subsingleton.elim _ _
    have hright : rgt ≫ iNB z = k ≫ c := Subsingleton.elim _ _
    have hleftOp : (iNB x).op ≫ l.op = a.op ≫ k.op := by
      simpa only [op_comp] using congrArg Quiver.Hom.op hleft
    have hrightOp : (iNB z).op ≫ rgt.op = c.op ≫ k.op := by
      simpa only [op_comp] using congrArg Quiver.Hom.op hright
    have hres : P.map l.op (φN x) = P.map rgt.op (φN z) := by
      dsimp only [φN]
      calc
        P.map l.op (P.map (iNB x).op (φ (b x))) =
            P.map ((iNB x).op ≫ l.op) (φ (b x)) := by
              rw [P.map_comp, ConcreteCategory.comp_apply]
        _ = P.map (a.op ≫ k.op) (φ (b x)) := by rw [hleftOp]
        _ = P.map k.op (P.map a.op (φ (b x))) := by
              rw [P.map_comp, ConcreteCategory.comp_apply]
        _ = P.map k.op (P.map c.op (φ (b z))) := congrArg _ heq
        _ = P.map (c.op ≫ k.op) (φ (b z)) := by
              rw [P.map_comp, ConcreteCategory.comp_apply]
        _ = P.map ((iNB z).op ≫ rgt.op) (φ (b z)) := by rw [hrightOp]
        _ = P.map rgt.op (P.map (iNB z).op (φ (b z))) := by
              rw [P.map_comp, ConcreteCategory.comp_apply]
    exact congrArg
      (fun θ ↦ singularCochainToSimplexFunction R X (.op (N x ⊓ N z)) n θ r)
      hres
  obtain ⟨ψ, hψ⟩ := exists_openCochain_of_compatibleOnSimplexBasis R X
    (U := .op U) (fun x : U ↦ .op (N x)) (fun x ↦ (iNU x).op) n φN (by
      intro x z sx sz hs
      obtain ⟨r, hrs, hrz⟩ := exists_openSimplex_inf_of_eq X (iNU x) (iNU z) n sx sz hs
      have heval := congrArg
        (fun θ ↦ singularCochainToSimplexFunction R X (.op (N x ⊓ N z)) n θ r)
        (hφN x z)
      have hl := congrFun (singularCochainToSimplexFunction_naturality R X
        (homOfLE inf_le_left).op n (φN x)) r
      have hr := congrFun (singularCochainToSimplexFunction_naturality R X
        (homOfLE inf_le_right).op n (φN z)) r
      calc
        singularCochainToSimplexFunction R X (.op (N x)) n (φN x) sx =
            singularCochainToSimplexFunction R X (.op (N x)) n (φN x)
              (openSimplexMap X (homOfLE inf_le_left).op n r) :=
          congrArg _ hrs.symm
        _ = singularCochainToSimplexFunction R X (.op (N x ⊓ N z)) n
              (P.map (homOfLE inf_le_left).op (φN x)) r := hl.symm
        _ = singularCochainToSimplexFunction R X (.op (N x ⊓ N z)) n
              (P.map (homOfLE inf_le_right).op (φN z)) r := heval
        _ = singularCochainToSimplexFunction R X (.op (N z)) n (φN z)
              (openSimplexMap X (homOfLE inf_le_right).op n r) := hr
        _ = singularCochainToSimplexFunction R X (.op (N z)) n (φN z) sz :=
          congrArg _ hrz)
  let t : ToType ((J.plusObj P).obj (.op U)) := (J.toPlus P).app (.op U) ψ
  have htN (x : U) :
      (J.plusObj P).map (iNU x).op t =
        (J.plusObj P).map (iNB x).op (s (b x)) := by
    let η := J.toPlus P
    calc
      (J.plusObj P).map (iNU x).op t =
          η.app (.op (N x)) (P.map (iNU x).op ψ) :=
            (ConcreteCategory.congr_hom (η.naturality (iNU x).op) ψ).symm
      _ = η.app (.op (N x)) (φN x) := congrArg _ (hψ x)
      _ = η.app (.op (N x)) (P.map (iNB x).op (φ (b x))) := rfl
      _ = (J.plusObj P).map (iNB x).op
          (η.app (.op (b x).Y) (φ (b x))) :=
            ConcreteCategory.congr_hom (η.naturality (iNB x).op) (φ (b x))
      _ = (J.plusObj P).map (iNB x).op (s (b x)) :=
        congrArg _ (hφ (b x))
  refine ⟨t, ?_⟩
  rw [GrothendieckTopology.Plus.toPlus_mk S t]
  congr 1
  apply Meq.ext
  intro I
  apply GrothendieckTopology.Plus.sep P
    ⟨openFamilySieve
        (fun x : I.Y ↦ N ⟨x.1, I.f.le x.2⟩ ⊓ I.Y)
        (fun _ ↦ inf_le_right),
      openFamilySieve_mem _ (fun _ ↦ inf_le_right) (by
        intro z hz
        let x : I.Y := ⟨z, hz⟩
        exact ⟨x, ⟨hxN ⟨x.1, I.f.le x.2⟩, x.2⟩⟩)⟩
  intro A
  obtain ⟨x, hAx⟩ := A.hf
  let xU : U := ⟨x.1, I.f.le x.2⟩
  let aN : A.Y ⟶ N xU := homOfLE (hAx.trans inf_le_left)
  let aI : A.Y ⟶ I.Y := A.f
  let aU : A.Y ⟶ U := A.f ≫ I.f
  let aB : A.Y ⟶ (b xU).Y := aN ≫ iNB xU
  have hleft : aI ≫ I.f = aN ≫ iNU xU := Subsingleton.elim _ _
  have hrestrict := congrArg
    (fun q ↦ (J.plusObj P).map aN.op q) (htN xU)
  have hrestrict' :
      (J.plusObj P).map aU.op t =
        (J.plusObj P).map aB.op (s (b xU)) := by
    have haU : aU = aN ≫ iNU xU := hleft
    have haB : aB = aN ≫ iNB xU := rfl
    rw [haU, haB, op_comp, op_comp, (J.plusObj P).map_comp,
      (J.plusObj P).map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply]
    exact hrestrict
  let rel : S.Relation := GrothendieckTopology.Cover.Relation.mk'
    { Z := A.Y
      g₁ := aB
      g₂ := aI }
  have hsrel := s.condition rel
  change (J.plusObj P).map aB.op (s (b xU)) =
    (J.plusObj P).map aI.op (s I) at hsrel
  change (J.plusObj P).map A.f.op
      ((J.plusObj P).map I.f.op t) =
    (J.plusObj P).map A.f.op (s I)
  rw [← ConcreteCategory.comp_apply, ← (J.plusObj P).map_comp,
    ← op_comp]
  exact hrestrict'.trans hsrel

/-- Flasqueness is invariant under isomorphism of additive presheaves. -/
lemma presheaf_isFlasque_of_iso
    {P Q : TopCat.Presheaf AddCommGrpCat X} (e : P ≅ Q) [P.IsFlasque] :
    Q.IsFlasque where
  epi {U V} i := by
    have hcomp : Epi (e.hom.app U ≫ Q.map i) := by
      rw [← e.hom.naturality i]
      infer_instance
    exact CategoryTheory.epi_of_epi (e.hom.app U) (Q.map i)

/-- On a hereditarily paracompact Hausdorff space, the degreewise double-plus singular-cochain
presheaves are flasque. -/
instance singularCochainPlusPlus_isFlasque
    [T2Space X] [∀ V : Opens X, ParacompactSpace V] (n : ℕ) :
    TopCat.Presheaf.IsFlasque
      ((Opens.grothendieckTopology X).plusObj
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n))) := by
  have hEpi : ∀ V : (Opens X)ᵒᵖ, Epi
      (((Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n))).app V) := by
    intro V
    rw [AddCommGrpCat.epi_iff_surjective]
    exact singularCochain_plusToPlus_surjective_on V.unop n
  exact @presheaf_isFlasque_of_epi X _ _
    ((Opens.grothendieckTopology X).toPlus
      ((Opens.grothendieckTopology X).plusObj
        (singularCochainPresheaf R X n))) inferInstance hEpi

/-- On a hereditarily paracompact Hausdorff space, every term of the sheafified rational singular
cochain complex is flasque. -/
instance singularCochainSheaf_isFlasque_of_opens_paracompact
    [T2Space X] [∀ V : Opens X, ParacompactSpace V] (n : ℕ) :
    TopCat.Sheaf.IsFlasque (singularCochainSheaf R X n) := by
  let J := Opens.grothendieckTopology X
  let P := singularCochainPresheaf R X n
  let e : J.sheafify P ≅ CategoryTheory.sheafify J P :=
    plusPlusIsoSheafify J AddCommGrpCat P
  change TopCat.Presheaf.IsFlasque (CategoryTheory.sheafify J P)
  let : TopCat.Presheaf.IsFlasque (J.sheafify P) :=
    singularCochainPlusPlus_isFlasque (R := R) (X := X) n
  exact presheaf_isFlasque_of_iso e

/-- On a paracompact Hausdorff space, the map from global first-plus cochains to global
double-plus cochains is an isomorphism of complexes. -/
noncomputable instance globalSingularCochainPlusToPlusPlusComplex_isIso
    [ParacompactSpace X] [T2Space X] :
    IsIso (globalSingularCochainPlusToPlusPlusComplex R X) := by
  let : ParacompactSpace (Set.univ : Set X) :=
    (Homeomorph.Set.univ X).paracompactSpace_iff.mpr inferInstance
  let : ∀ n : ℕ,
      IsIso ((globalSingularCochainPlusToPlusPlusComplex R X).f n) := by
    intro n
    change IsIso
      (((Opens.grothendieckTopology X).toPlus
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n))).app (.op ⊤))
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · apply GrothendieckTopology.Plus.inj_of_sep
        ((Opens.grothendieckTopology X).plusObj
          (singularCochainPresheaf R X n))
      intro V S x y h
      exact GrothendieckTopology.Plus.sep
        (singularCochainPresheaf R X n) S x y h
    · exact singularCochain_plusToPlus_surjective_on (⊤ : Opens X) n
  exact HomologicalComplex.Hom.isIso_of_components
    (globalSingularCochainPlusToPlusPlusComplex R X)

end HereditarilyParacompact

end AlgebraicTopology.Singular
