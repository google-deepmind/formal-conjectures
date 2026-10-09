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

import RestrictedWeilCriterionLaplaceV10
import BoundedZeroFinitenessV1
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Tactic

/-!
AEGIS Ω — isolated centered-zero pole geometry V10.

This module advances the restricted-Weil criterion past the Laplace seed
identity.  It proves that every nontrivial zeta zero gives an isolated centered
Cauchy pole.  The result uses Mathlib's pinned discreteness theorem for the
Riemann-zeta zero set and the exact isometry
  rho ↦ 1/2 - rho.

No positivity or RH conclusion is asserted here.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionPoleIsolationV10

open AEGIS.RestrictedWeilCriterionZeroKernelV10
open AEGIS.RestrictedWeilCriterionLaplaceV10

/-- Centering at 1/2 is injective on the canonical zero carrier. -/
theorem centeredZeroExponent_injective_v10 :
    Function.Injective CenteredZeroExponentV10 := by
  intro rho sigma h
  apply Subtype.ext
  unfold CenteredZeroExponentV10 at h
  linear_combination -h

/-- Centering preserves pairwise distances. -/
theorem dist_centeredZeroExponent_v10
    (rho sigma : RiemannNontrivialZeroIndexV2) :
    dist (CenteredZeroExponentV10 rho)
        (CenteredZeroExponentV10 sigma) =
      dist rho.1 sigma.1 := by
  rw [dist_eq, dist_eq]
  unfold CenteredZeroExponentV10
  have h :
      ((1 / 2 : ℂ) - rho.1) -
          ((1 / 2 : ℂ) - sigma.1) =
        -(rho.1 - sigma.1) := by
    ring
  rw [h, norm_neg]

/-- Every canonical centered zero has a positive isolation radius containing
no other centered zero. -/
theorem exists_centered_zero_isolation_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        dist (CenteredZeroExponentV10 sigma)
            (CenteredZeroExponentV10 rho) < ε →
          sigma = rho := by
  have hrhoZ : rho.1 ∈ riemannZetaZeros := by
    exact mem_riemannZetaZeros.mpr rho.2.1
  obtain ⟨ε, hε, hball⟩ :=
    exists_ball_inter_eq_singleton_of_mem_discrete
      isDiscrete_riemannZetaZeros hrhoZ
  refine ⟨ε, hε, ?_⟩
  intro sigma hsigma
  have hsigmaZ : sigma.1 ∈ riemannZetaZeros := by
    exact mem_riemannZetaZeros.mpr sigma.2.1
  have hdist : dist sigma.1 rho.1 < ε := by
    simpa [dist_comm] using
      (show
        dist (CenteredZeroExponentV10 sigma)
          (CenteredZeroExponentV10 rho) < ε from hsigma)
  have hmem :
      sigma.1 ∈ Metric.ball rho.1 ε ∩ riemannZetaZeros := by
    exact ⟨by simpa [Metric.mem_ball] using hdist, hsigmaZ⟩
  have hsingle : sigma.1 ∈ ({rho.1} : Set ℂ) := by
    rw [← hball]
    exact hmem
  have hval : sigma.1 = rho.1 := by
    simpa using hsingle
  exact Subtype.ext hval

/-- A distinct canonical zero stays outside the isolation ball. -/
theorem centered_zero_dist_ge_isolation_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ sigma : RiemannNontrivialZeroIndexV2,
        sigma ≠ rho →
        ε ≤
          dist (CenteredZeroExponentV10 sigma)
            (CenteredZeroExponentV10 rho) := by
  obtain ⟨ε, hε, hiso⟩ :=
    exists_centered_zero_isolation_v10 rho
  refine ⟨ε, hε, ?_⟩
  intro sigma hne
  by_contra hlt
  have : dist (CenteredZeroExponentV10 sigma)
      (CenteredZeroExponentV10 rho) < ε := lt_of_not_ge hlt
  exact hne (hiso sigma this)

end AEGIS.RestrictedWeilCriterionPoleIsolationV10

#print axioms AEGIS.RestrictedWeilCriterionPoleIsolationV10.centeredZeroExponent_injective_v10
#print axioms AEGIS.RestrictedWeilCriterionPoleIsolationV10.exists_centered_zero_isolation_v10
#print axioms AEGIS.RestrictedWeilCriterionPoleIsolationV10.centered_zero_dist_ge_isolation_v10
