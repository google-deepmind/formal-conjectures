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

import RestrictedWeilCriterionResidueWitnessV11
import RestrictedWeilCriterionLaplaceV10
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

/-!
AEGIS Ω — nonzero pole coefficient for each canonical nontrivial zeta zero.

The targeted V11 packet already makes the autocorrelation Mellin factor nonzero
at the selected zero.  This module discharges the remaining multiplicity
factor: a genuine zeta zero away from the pole s=1 has strictly positive
analytic order, hence nonzero natural multiplicity.

AUTHORITY_EFFECT = NONE.
-/

open Complex Set

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionResidueCoefficientV11

open AEGIS.RestrictedWeilCriterionResidueWitnessV11
open AEGIS.RestrictedWeilCriterionLaplaceV10

theorem zeta_analyticOrderNatAt_ne_zero_v11
    (rho : RiemannNontrivialZeroIndexV2) :
    analyticOrderNatAt riemannZeta rho.1 ≠ 0 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  have hr1 : rho.1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.2]

  have hAnal : AnalyticAt ℂ riemannZeta rho.1 :=
    analyticOn_riemannZeta rho.1 (by simpa using hr1)

  have hOrderNeZero :
      analyticOrderAt riemannZeta rho.1 ≠ 0 :=
    (hAnal.analyticOrderAt_ne_zero).2 rho.2.1

  have hPre :
      IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (rank_real_complex ▸ Nat.one_lt_ofNat) (1 : ℂ)).isPreconnected

  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simp
  have hrmem : rho.1 ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simpa using hr1

  have h2Anal : AnalyticAt ℂ riemannZeta (2 : ℂ) :=
    analyticOn_riemannZeta 2 (by simp)
  have hz2 : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have h2ord0 :
      analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
    (h2Anal.analyticOrderAt_eq_zero).2 hz2
  have h2finite :
      analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    rw [h2ord0]
    simp

  have hfinite :
      analyticOrderAt riemannZeta rho.1 ≠ ⊤ :=
    analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
      hPre h2mem hrmem h2finite

  intro hnat
  have hcast :
      analyticOrderAt riemannZeta rho.1 = 0 := by
    rw [← Nat.cast_analyticOrderNatAt hfinite]
    simp [hnat]
  exact hOrderNeZero hcast

/-- Every canonical nontrivial zero admits a moment-zero compact-smooth test
whose actual Cauchy-transform residue coefficient is nonzero. -/
theorem exists_nonzero_zero_coefficient_v11
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      ZeroCoefficientV10 g rho ≠ 0 := by
  obtain ⟨g, hm, hM⟩ :=
    exists_residue_packet_autocorrelation_mellin_ne_zero_v11 rho
  refine ⟨g, hm, ?_⟩
  unfold ZeroCoefficientV10
  have hmultNat :=
    zeta_analyticOrderNatAt_ne_zero_v11 rho
  have hmultC :
      ((analyticOrderNatAt riemannZeta rho.1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hmultNat
  exact mul_ne_zero hmultC hM

end AEGIS.RestrictedWeilCriterionResidueCoefficientV11

#print axioms AEGIS.RestrictedWeilCriterionResidueCoefficientV11.zeta_analyticOrderNatAt_ne_zero_v11
#print axioms AEGIS.RestrictedWeilCriterionResidueCoefficientV11.exists_nonzero_zero_coefficient_v11
