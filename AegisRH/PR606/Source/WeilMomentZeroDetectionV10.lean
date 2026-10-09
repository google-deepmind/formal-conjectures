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

import WeilFiniteDilationFilterV10
import WeilOffLineSeedV10
import ZeroCriticalStripV1
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic

/-!
AEGIS Ω — moment-zero spectral detection V10.

This module composes the exact two-point Mellin seed with the finite-dilation
moment filter.

For any two points s,t in the strict strip 0 < Re < 1 it produces a repository
packet g such that

* WeilMomentConditionsV1 g;
* M g(s) ≠ 0;
* M g(t) ≠ 0.

Specializing t = 1 - conj rho gives the exact nonvanishing pair required by
the off-line-zero residue obstruction.

AUTHORITY_EFFECT = NONE.
-/

open Complex Set
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilMomentZeroDetectionV10

open AEGIS.WeilFiniteDilationFilterV10
open AEGIS.WeilOffLineSeedV10

theorem exists_moment_zero_packet_detecting_pair_v10
    (s t : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht0 : 0 < t.re) (ht1 : t.re < 1) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin g.1 s ≠ 0 ∧
      mellin g.1 t ≠ 0 := by
  obtain ⟨h, hhs, hht⟩ :=
    exists_packet_mellin_ne_zero_pair_v10 s t
  let g := finiteDilationFilterV10 h
  refine ⟨g, finiteDilationFilter_moments_v10 h, ?_, ?_⟩
  · exact finiteDilationFilter_mellin_ne_zero_v10
      h s hs0 hs1 hhs
  · exact finiteDilationFilter_mellin_ne_zero_v10
      h t ht0 ht1 hht

/-- Every actual nontrivial zeta zero has a moment-zero test packet that sees
both members of its autocorrelation pairing nontrivially. -/
theorem exists_moment_zero_packet_detecting_zero_pair_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin g.1 rho.1 ≠ 0 ∧
      mellin g.1 (1 - conj rho.1) ≠ 0 := by
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2
  have hr0 : 0 < rho.1.re := hstrip.1
  have hr1 : rho.1.re < 1 := hstrip.2
  have ht0 : 0 < (1 - conj rho.1).re := by
    simp
    linarith
  have ht1 : (1 - conj rho.1).re < 1 := by
    simp
    linarith
  exact exists_moment_zero_packet_detecting_pair_v10
    rho.1 (1 - conj rho.1) hr0 hr1 ht0 ht1

/-- The multiplicity-weighted paired Mellin coefficient at every nontrivial
zero can be made nonzero by a repository-admissible moment-zero packet. -/
theorem exists_nonzero_zero_pair_coefficient_v10
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      ((analyticOrderNatAt riemannZeta rho.1 : ℂ) *
        (mellin g.1 rho.1 *
          conj (mellin g.1 (1 - conj rho.1)))) ≠ 0 := by
  obtain ⟨g, hm, h1, h2⟩ :=
    exists_moment_zero_packet_detecting_zero_pair_v10 rho
  have hmult : analyticOrderNatAt riemannZeta rho.1 ≠ 0 := by
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
  refine ⟨g, hm, ?_⟩
  apply mul_ne_zero
  · exact_mod_cast hmult
  · apply mul_ne_zero h1
    intro hc
    apply h2
    have hc' := congrArg conj hc
    simpa using hc'

end AEGIS.WeilMomentZeroDetectionV10

#print axioms AEGIS.WeilMomentZeroDetectionV10.exists_moment_zero_packet_detecting_pair_v10
#print axioms AEGIS.WeilMomentZeroDetectionV10.exists_moment_zero_packet_detecting_zero_pair_v10
#print axioms AEGIS.WeilMomentZeroDetectionV10.exists_nonzero_zero_pair_coefficient_v10
