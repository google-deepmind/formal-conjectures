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

public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularAffineSubdivisionIteration
public import FormalConjecturesForMathlib.Lemmas.AlgebraicTopology.SingularCoverSmallProjective

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# The algebraic endgame of the small-chain argument

This file separates the finite-chain algebra in the classical subdivision proof from the
geometric assertion that iterated affine subdivision eventually makes a chain subordinate to a
cover.  The abstract theorem says that a monomorphic inclusion of chain complexes is a
quasi-isomorphism when compatible endomorphisms on the source and target are homotopic to the
identity and every target chain is eventually carried into the image of the inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

section Abstract

variable {K L : ChainComplex AddCommGrpCat ℕ}

/-- Elementwise eventual factorization, together with compatible endomorphisms homotopic to the
identity, makes a monomorphic inclusion of nonnegative chain complexes a quasi-isomorphism.

The exponent is allowed to depend on the individual chain.  This is the form needed for singular
chains, whose elements have finite support but do not admit a uniform subdivision exponent. -/
public theorem chainComplex_quasiIso_of_eventually_factors
    (I : K ⟶ L) [Mono I]
    (smallIterate : ℕ → (K ⟶ K))
    (largeIterate : ℕ → (L ⟶ L))
    (hcompat : ∀ m, smallIterate m ≫ I = I ≫ largeIterate m)
    (hsmall : ∀ m, Homotopy (smallIterate m) (𝟙 K))
    (hlarge : ∀ m, Homotopy (largeIterate m) (𝟙 L))
    (heventually : ∀ (n : ℕ) (x : L.X n),
      ∃ (m : ℕ) (y : K.X n), I.f n y = (largeIterate m).f n x) :
    QuasiIso I := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    suffices a - b = 0 by exact sub_eq_zero.mp this
    let q : K.homology n := a - b
    have hqmap : HomologicalComplex.homologyMap I n q = 0 := by
      dsimp [q]
      rw [map_sub, hab, sub_self]
    obtain ⟨z, hz⟩ :=
      (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance q
    have hzmap :
        L.homologyπ n (HomologicalComplex.cyclesMap I n z) = 0 := by
      rw [← ConcreteCategory.comp_apply,
        ← HomologicalComplex.homologyπ_naturality,
        ConcreteCategory.comp_apply, hz]
      exact hqmap
    let T : ShortComplex AddCommGrpCat :=
      ShortComplex.mk (L.toCycles (n + 1) n) (L.homologyπ n) (by simp)
    have hT : T.Exact :=
      T.exact_of_g_is_cokernel (L.homologyIsCokernel (n + 1) n (by simp))
    obtain ⟨w, hw⟩ := (T.ab_exact_iff.mp hT)
      (HomologicalComplex.cyclesMap I n z) hzmap
    obtain ⟨m, w', hw'⟩ := heventually (n + 1) w
    have hzchain :
        I.f n (K.iCycles n z) = L.d (n + 1) n w := by
      rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.cyclesMap_i,
        ConcreteCategory.comp_apply, ← hw]
      dsimp [T]
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_i]
    have hboundary :
        (smallIterate m).f n (K.iCycles n z) = K.d (n + 1) n w' := by
      apply (AddCommGrpCat.mono_iff_injective (I.f n)).1
      · change Mono ((HomologicalComplex.eval AddCommGrpCat
            (ComplexShape.down ℕ) n).map I)
        infer_instance
      have hc := congrArg (fun F ↦ F.f n) (hcompat m)
      have hc' := ConcreteCategory.congr_hom hc (K.iCycles n z)
      simp only [HomologicalComplex.comp_f,
        ConcreteCategory.comp_apply] at hc'
      calc
        I.f n ((smallIterate m).f n (K.iCycles n z)) =
            (largeIterate m).f n (I.f n (K.iCycles n z)) := hc'
        _ = (largeIterate m).f n (L.d (n + 1) n w) := by rw [hzchain]
        _ = L.d (n + 1) n ((largeIterate m).f (n + 1) w) := by
          rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
            (largeIterate m).comm]
        _ = L.d (n + 1) n (I.f (n + 1) w') := by rw [← hw']
        _ = I.f n (K.d (n + 1) n w') := by
          rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, I.comm]
    have hiterzero :
        HomologicalComplex.homologyMap (smallIterate m) n
            (K.homologyπ n z) = 0 := by
      rw [← ConcreteCategory.comp_apply,
        HomologicalComplex.homologyπ_naturality,
        ConcreteCategory.comp_apply]
      let B : K.X (n + 1) ⟶ K.cycles n := K.toCycles (n + 1) n
      have hB : B w' =
          HomologicalComplex.cyclesMap (smallIterate m) n z := by
        apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).1 inferInstance
        calc
          K.iCycles n (B w') = K.d (n + 1) n w' := by
            rw [← ConcreteCategory.comp_apply]
            exact ConcreteCategory.congr_hom
              (HomologicalComplex.toCycles_i K (n + 1) n) w'
          _ = (smallIterate m).f n (K.iCycles n z) := hboundary.symm
          _ = K.iCycles n
              (HomologicalComplex.cyclesMap (smallIterate m) n z) :=
            ConcreteCategory.congr_hom
              (HomologicalComplex.cyclesMap_i (smallIterate m) n).symm z
      rw [← hB, ← ConcreteCategory.comp_apply,
        HomologicalComplex.toCycles_comp_homologyπ]
      rfl
    have hiter := congrArg (fun f ↦ f (K.homologyπ n z))
      ((hsmall m).homologyMap_eq n)
    rw [HomologicalComplex.homologyMap_id] at hiter
    change q = 0
    calc
      q = K.homologyπ n z := hz.symm
      _ = HomologicalComplex.homologyMap (smallIterate m) n
          (K.homologyπ n z) := by simpa using hiter.symm
      _ = 0 := hiterzero
  · intro y
    obtain ⟨z, rfl⟩ :=
      (AddCommGrpCat.epi_iff_surjective (L.homologyπ n)).1 inferInstance y
    let x : L.X n := L.iCycles n z
    obtain ⟨m, x', hx'⟩ := heventually n x
    let j : ℕ := (ComplexShape.down ℕ).next n
    have hxcycle : L.d n j x = 0 := by
      dsimp [x]
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
      rfl
    have hx'cycle : K.d n j x' = 0 := by
      apply (AddCommGrpCat.mono_iff_injective (I.f j)).1
      · change Mono ((HomologicalComplex.eval AddCommGrpCat
            (ComplexShape.down ℕ) j).map I)
        infer_instance
      rw [map_zero, ← ConcreteCategory.comp_apply, ← I.comm,
        ConcreteCategory.comp_apply, hx', ← ConcreteCategory.comp_apply,
        (largeIterate m).comm, ConcreteCategory.comp_apply, hxcycle, map_zero]
    have hx'mem : x' ∈ (K.sc n).g.hom.ker := by
      change (K.sc n).g x' = 0
      change K.d n ((ComplexShape.down ℕ).next n) x' = 0
      simpa [j] using hx'cycle
    let z' : K.cycles n :=
      (K.sc n).abCyclesIso.inv ⟨x', hx'mem⟩
    refine ⟨K.homologyπ n z', ?_⟩
    rw [← ConcreteCategory.comp_apply,
      HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    have hcycles : HomologicalComplex.cyclesMap I n z' =
        HomologicalComplex.cyclesMap (largeIterate m) n z := by
      apply (AddCommGrpCat.mono_iff_injective (L.iCycles n)).1 inferInstance
      calc
        L.iCycles n (HomologicalComplex.cyclesMap I n z') =
            I.f n (K.iCycles n z') := by
          rw [← ConcreteCategory.comp_apply,
            HomologicalComplex.cyclesMap_i,
            ConcreteCategory.comp_apply]
        _ = I.f n x' := by
          congr 1
          dsimp [z']
          exact (K.sc n).abCyclesIso_inv_apply_iCycles _
        _ = (largeIterate m).f n x := hx'
        _ = (largeIterate m).f n (L.iCycles n z) := rfl
        _ = L.iCycles n
            (HomologicalComplex.cyclesMap (largeIterate m) n z) :=
          ConcreteCategory.congr_hom
            (HomologicalComplex.cyclesMap_i (largeIterate m) n).symm z
    rw [hcycles, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
    have hiter := congrArg (fun f ↦ f (L.homologyπ n z))
      ((hlarge m).homologyMap_eq n)
    simpa using hiter

end Abstract

section Singular

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- Eventual smallness of every finite singular chain -- each is carried into the cover-small
subcomplex by some finite affine-subdivision iterate -- implies that the cover-small inclusion is
a quasi-isomorphism. -/
public theorem coverSmallChainQuasiIsomorphism_of_eventuallySmall
    (h : ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (CoverSmallIntegralSingularChainComplex X U).X n),
        (coverSmallIntegralSingularChainInclusion X U).f n y =
          (affineSingularSubdivisionIterate X m).f n x) :
    QuasiIso (coverSmallIntegralSingularChainInclusion X U) :=
  chainComplex_quasiIso_of_eventually_factors
    (coverSmallIntegralSingularChainInclusion X U)
    (coverSmallAffineSubdivisionIterate X U)
    (affineSingularSubdivisionIterate X)
    (coverSmallAffineSubdivisionIterate_comp_inclusion X U)
    (coverSmallAffineSubdivisionIterateHomotopy X U)
    (affineSingularSubdivisionIterateHomotopy X) h

/-- The same geometric input supplies the stronger chain-homotopy equivalence, via projectivity
of integral singular chain groups. -/
public theorem coverSmallChainApproximation_of_eventuallySmall
    (h : ∀ (n : ℕ) (x : (IntegralSingularChainComplexObj X).X n),
      ∃ (m : ℕ) (y : (CoverSmallIntegralSingularChainComplex X U).X n),
        (coverSmallIntegralSingularChainInclusion X U).f n y =
          (affineSingularSubdivisionIterate X m).f n x) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (coverSmallIntegralSingularChainInclusion X U) :=
  coverSmallChainApproximation_of_quasiIso X U
    (coverSmallChainQuasiIsomorphism_of_eventuallySmall X U h)

end Singular

end AlgebraicTopology.Singular
