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

import WeilAutocorrelationMellinV11
import WeilThreeBlockTranslatedPacketsV22
import ZeroCountingMellinSummabilityV1
import Mathlib.Tactic

/-!
AEGIS Ω — zero-side translation transport V11.

This module binds the repository translation packet to the centered Mellin
spectral factor:

  M(T_d g)(s) = exp((s - 1/2)d) M(g)(s).

Combining this with the full autocorrelation Mellin factorization from V11
shows that every individual nontrivial-zero summand of the autocorrelation
quadratic is invariant under translation.  Hence the canonical absolutely
convergent zero quadratic itself is translation invariant.

This is one of the exact algebraic inputs for the restricted Weil two-point
criterion.  No positivity or RH conclusion is asserted.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex
open scoped BigOperators

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilZeroTranslationV11

open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.WeilAutocorrelationMellinV11

/-- Exact Mellin transport law for the repository's centered translation. -/
theorem mellin_translatePacket_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) (s : ℂ) :
    mellin (translatePacket g d).1 s =
      Complex.exp ((s - (1 / 2 : ℂ)) * (d : ℂ)) *
        mellin g.1 s := by
  have hc :=
    mellin_const_smul
      (fun x : ℝ => g.1 (Real.exp (-d) * x))
      s (Real.exp (-d / 2) : ℂ)
  simp only [smul_eq_mul] at hc
  have hmul :=
    mellin_comp_mul_left g.1 s (Real.exp_pos (-d))
  change
    mellin
      (fun x : ℝ =>
        (Real.exp (-d / 2) : ℂ) *
          g.1 (Real.exp (-d) * x)) s = _
  rw [hc, hmul]
  simp only [smul_eq_mul]
  have hpow :
      (((Real.exp (-d) : ℝ) : ℂ) ^ (-s)) =
        Complex.exp (s * (d : ℂ)) := by
    have hne : (((Real.exp (-d) : ℝ) : ℂ) ≠ 0) := by
      exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    rw [Complex.cpow_def_of_ne_zero hne]
    have hlog :
        Complex.log (((Real.exp (-d) : ℝ) : ℂ)) = (-d : ℂ) := by
      rw [← Complex.ofReal_log (Real.exp_pos (-d)).le, Real.log_exp]
    rw [hlog]
    congr 1
    ring
  rw [hpow, ← Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Repository zero summand written in the full Mellin-factorized
autocorrelation form. -/
theorem autocorrelation_zero_summand_factorization_v11
    (g : WeilCompactSmoothGV1)
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho =
      (analyticOrderNatAt riemannZeta rho.1 : ℂ) *
        (mellin g.1 rho.1 *
          conj (mellin g.1 (1 - conj rho.1))) := by
  unfold WeilZeroIndexSummandV1
  rw [weil_autocorrelation_mellin_factorization_v11]
  ring

/-- The centered translation factors cancel pointwise in the autocorrelation
zero summand. -/
theorem translated_autocorrelation_zero_summand_invariant_v11
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (rho : RiemannNontrivialZeroIndexV2) :
    WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 (translatePacket g d)) rho =
      WeilZeroIndexSummandV1
        (WeilAutocorrelationV1 g) rho := by
  rw [autocorrelation_zero_summand_factorization_v11,
    autocorrelation_zero_summand_factorization_v11,
    mellin_translatePacket_v11,
    mellin_translatePacket_v11]
  have hexp_conj :
      conj
        (Complex.exp
          (((1 - conj rho.1) - (1 / 2 : ℂ)) * (d : ℂ))) =
        Complex.exp
          (-((rho.1 - (1 / 2 : ℂ)) * (d : ℂ))) := by
    rw [map_exp]
    congr 1
    push_cast
    ring
  rw [map_mul, hexp_conj, ← mul_assoc]
  have hcancel :
      Complex.exp ((rho.1 - (1 / 2 : ℂ)) * (d : ℂ)) *
        Complex.exp (-((rho.1 - (1 / 2 : ℂ)) * (d : ℂ))) = 1 := by
    rw [← Complex.exp_add]
    simp
  ring_nf
  rw [hcancel]
  ring

/-- Canonical zero quadratic attached to an autocorrelation. -/
def WeilAutocorrelationZeroQuadraticV11
    (g : WeilCompactSmoothGV1) : ℂ :=
  ∑' rho : RiemannNontrivialZeroIndexV2,
    WeilZeroIndexSummandV1 (WeilAutocorrelationV1 g) rho

/-- The absolutely convergent zero quadratic is translation invariant. -/
theorem autocorrelation_zero_quadratic_translate_invariant_v11
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    WeilAutocorrelationZeroQuadraticV11 (translatePacket g d) =
      WeilAutocorrelationZeroQuadraticV11 g := by
  unfold WeilAutocorrelationZeroQuadraticV11
  apply tsum_congr
  intro rho
  exact translated_autocorrelation_zero_summand_invariant_v11 g d rho

end AEGIS.WeilZeroTranslationV11

#print axioms AEGIS.WeilZeroTranslationV11.mellin_translatePacket_v11
#print axioms AEGIS.WeilZeroTranslationV11.autocorrelation_zero_summand_factorization_v11
#print axioms AEGIS.WeilZeroTranslationV11.translated_autocorrelation_zero_summand_invariant_v11
#print axioms AEGIS.WeilZeroTranslationV11.autocorrelation_zero_quadratic_translate_invariant_v11
