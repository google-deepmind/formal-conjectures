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

import WeilReciprocalPairedTestV8
import WeilDigammaSeriesHalfPlaneV1

/-!
AEGIS Ω — fixed-line gamma normalization core V10.

This module binds the already proved V6 Mellin inversion theorem to the actual
V5 paired Mellin profile through the concrete V8 reciprocal-paired test.

It proves the two fixed-line evaluations consumed by the normalized gamma
term:

  (2π)⁻¹ ∫ H(c+it) dt = 2 f(1)

and, for every real u,

  (2π)⁻¹ ∫ exp (-(c+it)u/2) H(c+it) dt
    = q(exp(u/2)),

where q(x)=f(x)+x⁻¹ f(x⁻¹).

No new Fubini exchange is performed here.  The remaining V10 gamma step is
precisely the product-integrability/swap for the Gauss kernel.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilFixedLineGammaCoreV10

/-- The normalized integral of the actual paired Mellin profile is exactly
the paired test at x=1, hence 2 f(1). -/
theorem weil_paired_profile_integral_one_v10
    (f : WeilCompactSmoothGV1) (c : ℝ) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, WeilPairedMellinProfileV5 f c t) =
      2 * f.1 1 := by
  have h :=
    weil_compact_smooth_mellin_inversion_exp_line_v6
      (WeilPairedTestV8 f) c 0
  have hprofile :
      ∀ t : ℝ,
        WeilFixedLineMellinV6 (WeilPairedTestV8 f) c t =
          WeilPairedMellinProfileV5 f c t := by
    intro t
    exact weil_paired_test_fixed_line_profile_v8 f c t
  simp_rw [hprofile] at h
  simp [WeilPairedTestV8, WeilReciprocalFnV8] at h ⊢
  rw [h]
  ring

/-- Mellin inversion for the actual paired profile at x=exp(u/2). -/
theorem weil_paired_profile_exp_half_integral_v10
    (f : WeilCompactSmoothGV1) (c u : ℝ) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        Complex.exp
          (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ))) *
          WeilPairedMellinProfileV5 f c t) =
      (WeilPairedTestV8 f).1 (Real.exp (u / 2)) := by
  have h :=
    weil_compact_smooth_mellin_inversion_exp_line_v6
      (WeilPairedTestV8 f) c (u / 2)
  have hprofile :
      ∀ t : ℝ,
        WeilFixedLineMellinV6 (WeilPairedTestV8 f) c t =
          WeilPairedMellinProfileV5 f c t := by
    intro t
    exact weil_paired_test_fixed_line_profile_v8 f c t
  simp_rw [hprofile] at h
  exact h

/-- Expanded form of the previous theorem in terms of the original test and
its reciprocal partner. -/
theorem weil_paired_profile_exp_half_integral_expanded_v10
    (f : WeilCompactSmoothGV1) (c u : ℝ) :
    ((1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ,
        Complex.exp
          (-(((c : ℂ) + (t : ℂ) * I) * ((u / 2 : ℝ) : ℂ))) *
          WeilPairedMellinProfileV5 f c t) =
      f.1 (Real.exp (u / 2)) +
        ((Real.exp (-(u / 2)) : ℝ) : ℂ) *
          f.1 (Real.exp (-(u / 2))) := by
  rw [weil_paired_profile_exp_half_integral_v10 f c u]
  simp only [WeilPairedTestV8, WeilReciprocalFnV8]
  have hinv : (Real.exp (u / 2))⁻¹ = Real.exp (-(u / 2)) := by
    rw [← Real.exp_neg]
  rw [hinv]

end AEGIS.WeilFixedLineGammaCoreV10

#print axioms AEGIS.WeilFixedLineGammaCoreV10.weil_paired_profile_integral_one_v10
#print axioms AEGIS.WeilFixedLineGammaCoreV10.weil_paired_profile_exp_half_integral_v10
#print axioms AEGIS.WeilFixedLineGammaCoreV10.weil_paired_profile_exp_half_integral_expanded_v10
