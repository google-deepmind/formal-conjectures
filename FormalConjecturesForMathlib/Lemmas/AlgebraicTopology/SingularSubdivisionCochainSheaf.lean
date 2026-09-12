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

public import FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularSubdivisionCochainSheaf

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.ShrinkingLemma

/-!
# Global and locally defined singular cochains

Lemmas about the definitions in
`FormalConjecturesForMathlib.Definitions.AlgebraicTopology.SingularSubdivisionCochainSheaf`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Inclusion of an open subset into the top open, followed by inclusion of the top open into the
space, is the usual subspace inclusion. -/
lemma openToTop_comp_inclusionTopIso {V : Opens X} (i : V ⟶ ⊤) :
    (Opens.toTopCat X).map i ≫ (Opens.inclusionTopIso X).hom =
      topologicalSubsetInclusion X V :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The corresponding identity on singular chain complexes. -/
lemma openSingularChainToTop_comp_topOpenIso {V : Opens X} (i : V ⟶ ⊤) :
    (openSingularChainComplexFunctor R X).map i ≫
        (topOpenSingularChainComplexIso R X).hom =
      SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion X V))
        (ModuleCat.of R R) := by
  change ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map ((Opens.toTopCat X).map i) ≫
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)).map (Opens.inclusionTopIso X).hom = _
  rw [← Functor.map_comp, openToTop_comp_inclusionTopIso]
  rfl

/-- Every term of the double-plus singular-cochain complex satisfies the sheaf condition. -/
lemma singularCochainPlusPlusPresheafComplex_isSheaf (n : ℕ) :
    TopCat.Presheaf.IsSheaf
      ((singularCochainPlusPlusPresheafComplex R X).X n) := by
  change CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology X).plusObj
      ((Opens.grothendieckTopology X).plusObj
        (singularCochainPresheaf R X n)))
  exact GrothendieckTopology.Plus.isSheaf_plus_plus
    (Opens.grothendieckTopology X) (singularCochainPresheaf R X n)

section RationalCover

variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

lemma coveringSieveOpenFamily_isOpen
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (I : S.Arrow) :
    IsOpen (coveringSieveOpenFamily Y S I) :=
  I.Y.2

/-- The domains of the arrows in a covering sieve of the top open subset cover the space. -/
lemma coveringSieveOpenFamily_iUnion
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) :
    ⋃ I, coveringSieveOpenFamily Y S I = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨V, f, hf, hy⟩ :=
    ((Opens.mem_grothendieckTopology Y).mp S.2) y trivial
  exact Set.mem_iUnion.mpr ⟨GrothendieckTopology.Cover.Arrow.mk V f hf, hy⟩

@[reassoc]
lemma coverMemberToSmallRationalSingularChains_comp_inclusion (j : κ) :
    coverMemberToSmallRationalSingularChains Y U j ≫
        coverSmallRationalSingularChainInclusion Y U =
      SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (U j)))
        (ModuleCat.of ℚ ℚ) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (coverMemberToSmallSingularSet Y U j) ≫
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (coverSmallSingularSubcomplex Y U).ι = _
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every member of a covering sieve implies vanishing on all chains subordinate
to the associated family of open subsets. -/
lemma rationalCochainRestrictionToCoveringSieve_eq_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.X n)
    (hφ : ∀ I : S.Arrow,
      (singularCochainPresheaf ℚ Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen ℚ Y).hom.f n φ) = 0) :
    (rationalCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ = 0 := by
  change Module.Dual ℚ
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n) at φ
  change ((coverSmallRationalSingularChainInclusion Y
    (coveringSieveOpenFamily Y S)).f n).hom.dualMap φ = 0
  apply_fun ModuleCat.ofHom
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨I, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (coveringSieveOpenFamily Y S) x.1).mp x.2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hI := congrArg
    (fun ψ : OpenCochains ℚ Y (.op I.Y) n ↦ ψ
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) y).hom a))
    (hφ I)
  dsimp only [singularCochainPresheaf, singularCochainComplexIsoTopOpen,
    HomologicalComplex.linearDualIso, HomologicalComplex.linearDualMap] at hI
  change φ (ModuleCat.Hom.hom
      (((openSingularChainComplexFunctor ℚ Y).map I.f).f n ≫
        (topOpenSingularChainComplexIso ℚ Y).hom.f n)
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) y).hom a)) = 0 at hI
  have hchain := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso ℚ Y I.f) n
  have hchain' :
      ((openSingularChainComplexFunctor ℚ Y).map I.f).f n ≫
          (topOpenSingularChainComplexIso ℚ Y).hom.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
          (ModuleCat.of ℚ ℚ)).f n := by
    simpa only [HomologicalComplex.comp_f] using hchain
  rw [hchain'] at hI
  have hiota := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I)))
      (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map (topologicalSubsetInclusion Y
        (coveringSieveOpenFamily Y S I)))
      (ModuleCat.of ℚ ℚ) y) a
  simp only [ConcreteCategory.comp_apply] at hiota
  have hI' : φ
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of ℚ ℚ)
        ((TopCat.toSSet.map (topologicalSubsetInclusion Y
          (coveringSieveOpenFamily Y S I))).app _ y)).hom a) = 0 := by
    calc
      _ = φ ((SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y
            (coveringSieveOpenFamily Y S I)))
          (ModuleCat.of ℚ ℚ)).f n
          (((TopCat.toSSet.obj
            (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
              (R := ModuleCat.of ℚ ℚ) y).hom a)) := congrArg φ hiota.symm
      _ = 0 := hI
  change φ (ModuleCat.Hom.hom
    (((coverSmallSingularSubcomplex Y
      (coveringSieveOpenFamily Y S) : SSet).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) x) ≫
      (coverSmallRationalSingularChainInclusion Y
        (coveringSieveOpenFamily Y S)).f n) a) = 0
  dsimp only [coverSmallRationalSingularChainInclusion] at ⊢
  rw [SSet.ι_chainComplexMap_f]
  simpa [hy] using hI'
  · intro f g h
    exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, vanishing on the cover-small chains associated to a covering sieve implies
vanishing after restriction along every arrow of that sieve. -/
lemma rationalCochainRestrictionToCoveringSieve_local_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.X n)
    (hφ : (rationalCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ = 0) :
    ∀ I : S.Arrow,
      (singularCochainPresheaf ℚ Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen ℚ Y).hom.f n φ) = 0 := by
  intro I
  change Module.Dual ℚ
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ)).X n) at φ
  change ((coverSmallRationalSingularChainInclusion Y
    (coveringSieveOpenFamily Y S)).f n).hom.dualMap φ = 0 at hφ
  change (((openSingularChainComplexFunctor ℚ Y).map I.f).f n).hom.dualMap
    (((topOpenSingularChainComplexIso ℚ Y).hom.f n).hom.dualMap φ) = 0
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hφ
    (((coverMemberToSmallRationalSingularChains Y
      (coveringSieveOpenFamily Y S) I).f n).hom c)
  have htop := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso ℚ Y I.f) n
  have hmember := HomologicalComplex.congr_hom
    (coverMemberToSmallRationalSingularChains_comp_inclusion Y
      (coveringSieveOpenFamily Y S) I) n
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hc ⊢
  calc
    φ ((topOpenSingularChainComplexIso ℚ Y).hom.f n
        (((openSingularChainComplexFunctor ℚ Y).map I.f).f n c)) =
      φ ((SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
        (ModuleCat.of ℚ ℚ)).f n c) :=
          congrArg φ (ConcreteCategory.congr_hom htop c)
    _ = φ ((coverSmallRationalSingularChainInclusion Y
          (coveringSieveOpenFamily Y S)).f n
        ((coverMemberToSmallRationalSingularChains Y
          (coveringSieveOpenFamily Y S) I).f n c)) :=
            congrArg φ (ConcreteCategory.congr_hom hmember c).symm
    _ = 0 := hc

lemma rationalCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
      rationalCochainRestrictionToCoverSmall Y U := by
  dsimp [rationalCochainHomotopyEquivCoverSmall,
    rationalCochainRestrictionToCoverSmall]
  change HomologicalComplex.linearDualMap
      (coverSmallRationalChainHomotopyEquiv_of_openCover
        Y U hUopen hUcover).hom = _
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom]

/-- Restriction from all rational cochains to cover-small cochains is a quasi-isomorphism for an
open cover. -/
theorem rationalCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (rationalCochainRestrictionToCoverSmall Y U) := by
  rw [← rationalCochainHomotopyEquivCoverSmall_hom Y U hUopen hUcover]
  infer_instance

/-- The complex of rational cochains vanishing on every chain subordinate to an open cover is
acyclic. -/
theorem rationalCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (rationalCochainRestrictionToCoverSmall Y U)).Acyclic := by
  let := rationalCochainRestrictionToCoverSmall_quasiIso Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (rationalCochainRestrictionToCoverSmall Y U)

set_option backward.isDefEq.respectTransparency false in
/-- A closed rational cochain which vanishes on all cover-small chains has a primitive which
also vanishes on all cover-small chains. -/
theorem exists_coverSmallKernel_primitive
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.X n)
    (hφsmall : (rationalCochainRestrictionToCoverSmall Y U).f n φ = 0)
    (hφclosed : (((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.d n (n + 1)) φ = 0) :
    ∃ ψ : ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.X
          ((ComplexShape.up ℕ).prev n),
      (((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of ℚ ℚ)).linearDualCochainComplex.sc n).f ψ = φ ∧
        (rationalCochainRestrictionToCoverSmall Y U).f
          ((ComplexShape.up ℕ).prev n) ψ = 0 := by
  let F := ((TopCat.toSSet.obj Y).chainComplex
    (ModuleCat.of ℚ ℚ)).linearDualCochainComplex
  let q := rationalCochainRestrictionToCoverSmall Y U
  let K := kernel q
  let E : (kernel q).X n ≅ ModuleCat.of ℚ (q.f n).hom.ker :=
    asIso (kernelComparison q (HomologicalComplex.eval (ModuleCat ℚ)
      (ComplexShape.up ℕ) n)) ≪≫ ModuleCat.kernelIsoKer (q.f n)
  let z : (kernel q).X n := E.inv ⟨φ, hφsmall⟩
  have hzmap : (kernel.ι q).f n z = φ := by
    let ev := HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.up ℕ) n
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι q ev) z
    have hk := ModuleCat.kernelIsoKer_hom_ker_subtype_apply
      (q.f n) ((kernelComparison q ev) z)
    have hE : E.hom z = (⟨φ, hφsmall⟩ : (q.f n).hom.ker) := by
      simp [z]
    calc
      (kernel.ι q).f n z = kernel.ι (ev.map q) ((kernelComparison q ev) z) := hc.symm
      _ = ((ModuleCat.kernelIsoKer (q.f n)).hom
          ((kernelComparison q ev) z)).1 := hk.symm
      _ = φ := congrArg Subtype.val hE
  have hzclosed : (K.sc n).g z = 0 := by
    change K.d n ((ComplexShape.up ℕ).next n) z = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    apply (ModuleCat.mono_iff_injective ((kernel.ι q).f (n + 1))).mp inferInstance
    rw [map_zero]
    change (K.d n (n + 1) ≫ (kernel.ι q).f (n + 1)) z = 0
    rw [← (kernel.ι q).comm n (n + 1)]
    change F.d n (n + 1) ((kernel.ι q).f n z) = 0
    rw [hzmap]
    exact hφclosed
  have hacyclic := rationalCoverSmallCochainKernel_acyclic Y U hUopen hUcover
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff (K.sc n)).mp
    (hacyclic n) z hzclosed
  change K.X ((ComplexShape.up ℕ).prev n) at p
  change K.d ((ComplexShape.up ℕ).prev n) n p = z at hp
  refine ⟨(kernel.ι q).f ((ComplexShape.up ℕ).prev n) p, ?_, ?_⟩
  · change F.d ((ComplexShape.up ℕ).prev n) n
      ((kernel.ι q).f ((ComplexShape.up ℕ).prev n) p) = φ
    calc
      _ = (kernel.ι q).f n
          (K.d ((ComplexShape.up ℕ).prev n) n p) :=
        by
          simpa only [ConcreteCategory.comp_apply, F, K] using
            (ConcreteCategory.congr_hom
              ((kernel.ι q).comm ((ComplexShape.up ℕ).prev n) n) p)
      _ = φ := by rw [hp, hzmap]
  · have hcondition := HomologicalComplex.congr_hom (kernel.condition q)
      ((ComplexShape.up ℕ).prev n)
    exact ConcreteCategory.congr_hom hcondition p

set_option backward.isDefEq.respectTransparency false in
/-- A closed cochain on the top open which vanishes along a covering sieve has a primitive that
still vanishes along the same sieve. -/
theorem exists_topOpenLocallyZero_primitive
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.X n)
    (hφlocal : ∀ I : S.Arrow,
      (singularCochainPresheaf ℚ Y n).map I.f.op φ = 0)
    (hφclosed : ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0) :
    ∃ ψ : (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.X
        ((ComplexShape.up ℕ).prev n),
      ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (singularCochainPresheaf ℚ Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  let A := (SingularChainComplex ℚ Y).linearDualCochainComplex
  let B := (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
  let e := singularCochainComplexIsoTopOpen ℚ Y
  let φ' : A.X n := e.inv.f n φ
  have heφ : e.hom.f n φ' = φ := by
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id n) φ
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      HomologicalComplex.id_f, ConcreteCategory.id_apply, φ'] using hc
  have hlocal' : ∀ I : S.Arrow,
      (singularCochainPresheaf ℚ Y n).map I.f.op (e.hom.f n φ') = 0 := by
    intro I
    rw [heφ]
    exact hφlocal I
  have hsmall : (rationalCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ' = 0 :=
    rationalCochainRestrictionToCoveringSieve_eq_zero Y S n φ' hlocal'
  have hclosed' : A.d n (n + 1) φ' = 0 := by
    change A.d n (n + 1) (e.inv.f n φ) = 0
    have hc := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) φ
    calc
      _ = e.inv.f (n + 1) (B.d n (n + 1) φ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = 0 := by rw [hφclosed, map_zero]
  obtain ⟨ψ, hψ, hψsmall⟩ := exists_coverSmallKernel_primitive Y
    (coveringSieveOpenFamily Y S)
    (coveringSieveOpenFamily_isOpen Y S)
    (coveringSieveOpenFamily_iUnion Y S) n φ' hsmall hclosed'
  change A.X ((ComplexShape.up ℕ).prev n) at ψ
  change A.d ((ComplexShape.up ℕ).prev n) n ψ = φ' at hψ
  refine ⟨e.hom.f ((ComplexShape.up ℕ).prev n) ψ, ?_, ?_⟩
  · change B.d ((ComplexShape.up ℕ).prev n) n
      (e.hom.f ((ComplexShape.up ℕ).prev n) ψ) = φ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    calc
      _ = e.hom.f n (A.d ((ComplexShape.up ℕ).prev n) n ψ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = e.hom.f n φ' := congrArg (e.hom.f n) hψ
      _ = φ := heφ
  · simpa only [e] using
      (rationalCochainRestrictionToCoveringSieve_local_zero
        Y S ((ComplexShape.up ℕ).prev n) ψ hψsmall)

set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel of the map from top-open rational cochains to global first-plus cochains is
acyclic. -/
theorem topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic :
    (kernel (topOpenToGlobalSingularCochainPlusComplex ℚ Y)).Acyclic := by
  let C := globalRawSingularCochainComplex ℚ Y
  let B := topOpenForgottenSingularCochainComplex ℚ Y
  let e := globalRawSingularCochainComplexIso ℚ Y
  let f := topOpenToGlobalSingularCochainPlusComplex ℚ Y
  let K := kernel f
  intro n
  rw [K.exactAt_iff, ShortComplex.ab_exact_iff]
  intro z hzclosed
  let φ : OpenCochains ℚ Y (.op ⊤) n := (kernel.ι f).f n z
  have hφplus : f.f n φ = 0 := by
    have hcondition := HomologicalComplex.congr_hom (kernel.condition f) n
    exact ConcreteCategory.congr_hom hcondition z
  change ((Opens.grothendieckTopology Y).toPlus
    (singularCochainPresheaf ℚ Y n)).app (.op ⊤) φ = 0 at hφplus
  obtain ⟨S, hφlocal⟩ :=
    (singularCochain_toPlus_eq_zero_iff ℚ Y ⊤ n φ).mp hφplus
  have hφclosed : ((TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0 := by
    change K.d n ((ComplexShape.up ℕ).next n) z = 0 at hzclosed
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hzclosed
    apply_fun (kernel.ι f).f (n + 1) at hzclosed
    rw [map_zero] at hzclosed
    have hc := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) z
    have hC : C.d n (n + 1) φ = 0 := by
      calc
        _ = (kernel.ι f).f (n + 1) (K.d n (n + 1) z) := by
          simpa only [ConcreteCategory.comp_apply, C, K] using hc
        _ = 0 := hzclosed
    change B.d n (n + 1) φ = 0
    have hc := ConcreteCategory.congr_hom (e.hom.comm n (n + 1)) φ
    have hc' : B.d n (n + 1) φ = C.d n (n + 1) φ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    rw [hc', hC]
  obtain ⟨ψ, hψ, hψlocal⟩ :=
    exists_topOpenLocallyZero_primitive Y S n φ hφlocal hφclosed
  have hψplus : f.f ((ComplexShape.up ℕ).prev n) ψ = 0 := by
    change ((Opens.grothendieckTopology Y).toPlus
      (singularCochainPresheaf ℚ Y ((ComplexShape.up ℕ).prev n))).app
        (.op ⊤) ψ = 0
    exact (singularCochain_toPlus_eq_zero_iff ℚ Y ⊤
      ((ComplexShape.up ℕ).prev n) ψ).mpr ⟨S, hψlocal⟩
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ)
    ((ComplexShape.up ℕ).prev n)
  let E : K.X ((ComplexShape.up ℕ).prev n) ≅
      AddCommGrpCat.of (f.f ((ComplexShape.up ℕ).prev n)).hom.ker :=
    asIso (kernelComparison f ev) ≪≫
      AddCommGrpCat.kernelIsoKer (f.f ((ComplexShape.up ℕ).prev n))
  let p : K.X ((ComplexShape.up ℕ).prev n) := E.inv ⟨ψ, hψplus⟩
  have hpmap : (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p = ψ := by
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι f ev) p
    have hk := ConcreteCategory.congr_hom
      (AddCommGrpCat.kernelIsoKer_hom_comp_subtype
        (f.f ((ComplexShape.up ℕ).prev n))) ((kernelComparison f ev) p)
    have hE : E.hom p =
        (⟨ψ, hψplus⟩ : (f.f ((ComplexShape.up ℕ).prev n)).hom.ker) := by
      simp [p]
    calc
      (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p =
          kernel.ι (ev.map f) ((kernelComparison f ev) p) := hc.symm
      _ = ((AddCommGrpCat.kernelIsoKer
          (f.f ((ComplexShape.up ℕ).prev n))).hom
            ((kernelComparison f ev) p)).1 := hk.symm
      _ = ψ := congrArg Subtype.val hE
  refine ⟨p, ?_⟩
  change K.d ((ComplexShape.up ℕ).prev n) n p = z
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).f n)).mp inferInstance
  have hc := ConcreteCategory.congr_hom
    ((kernel.ι f).comm ((ComplexShape.up ℕ).prev n) n) p
  have hψC : C.d ((ComplexShape.up ℕ).prev n) n ψ = φ := by
    change B.d ((ComplexShape.up ℕ).prev n) n ψ = φ at hψ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    have hc' : B.d ((ComplexShape.up ℕ).prev n) n ψ =
        C.d ((ComplexShape.up ℕ).prev n) n ψ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    exact hc'.symm.trans hψ
  calc
    (kernel.ι f).f n (K.d ((ComplexShape.up ℕ).prev n) n p) =
        C.d ((ComplexShape.up ℕ).prev n) n
          ((kernel.ι f).f ((ComplexShape.up ℕ).prev n) p) := by
      simpa only [ConcreteCategory.comp_apply, C, K] using hc.symm
    _ = C.d ((ComplexShape.up ℕ).prev n) n ψ := by rw [hpmap]
    _ = φ := hψC
    _ = (kernel.ι f).f n z := rfl

/-- The map from top-open rational cochains to global first-plus cochains is a
quasi-isomorphism. -/
theorem topOpenToGlobalSingularCochainPlusComplex_quasiIso :
    QuasiIso (topOpenToGlobalSingularCochainPlusComplex ℚ Y) :=
  HomologicalComplex.quasiIso_of_epi_of_kernel_acyclic
    (topOpenToGlobalSingularCochainPlusComplex ℚ Y)
    (topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic Y)

set_option backward.isDefEq.respectTransparency false in
lemma topOpenRationalCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (topOpenRationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
      topOpenRationalCochainRestrictionToCoverSmall Y U := by
  change (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
    (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      rationalCochainRestrictionToCoverSmall Y U
  rw [rationalCochainHomotopyEquivCoverSmall_hom]

/-- For an open cover, restriction from top-open rational cochains to cover-small cochains is a
quasi-isomorphism. -/
theorem topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (topOpenRationalCochainRestrictionToCoverSmall Y U) := by
  rw [← topOpenRationalCochainHomotopyEquivCoverSmall_hom Y U hUopen hUcover]
  infer_instance

/-- The complex of top-open rational cochains vanishing on all chains subordinate to an open
cover is acyclic. -/
theorem topOpenRationalCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (topOpenRationalCochainRestrictionToCoverSmall Y U)).Acyclic := by
  let := topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (topOpenRationalCochainRestrictionToCoverSmall Y U)

end RationalCover

section HereditarilyParacompact

variable {R : Type u} [Field R] {X : TopCat.{u}}

/-- Every positive sheaf-cohomology group of a term of the singular-cochain resolution vanishes
on a hereditarily paracompact Hausdorff space. -/
lemma singularCochainSheaf_cohomology_succ_eq_zero
    [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (n q : ℕ) (x : Abelian.Ext
      (TopCat.Sheaf.IsFlasque.globalSectionsSource (X := X))
      (singularCochainSheaf R X n) (q + 1)) :
    x = 0 :=
  TopCat.Sheaf.IsFlasque.cohomology_succ_eq_zero
    (singularCochainSheaf R X n) q x

/-- On a paracompact Hausdorff space, ordinary cochains map quasi-isomorphically to global
sections of the double-plus singular-cochain complex. -/
theorem topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainPlusPlusComplex ℚ Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusComplex ℚ Y ≫
      globalSingularCochainPlusToPlusPlusComplex ℚ Y)
  let := topOpenToGlobalSingularCochainPlusComplex_quasiIso Y
  infer_instance

/-- On a paracompact Hausdorff space, ordinary rational singular cochains compute the global
section complex of the chosen singular-cochain sheaf resolution. -/
theorem topOpenToGlobalSingularCochainSheafComplex_quasiIso
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainSheafComplex ℚ Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusPlusComplex ℚ Y ≫
      (globalSingularCochainPlusPlusComplexIsoSheafComplex ℚ Y).hom)
  let := topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso (Y := Y)
  infer_instance

end HereditarilyParacompact

end AlgebraicTopology.Singular
