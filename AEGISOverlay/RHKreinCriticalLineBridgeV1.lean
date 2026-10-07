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
import RHKreinPairingV13
import Mathlib.Tactic

/-!
# Critical-line Mellin/Fourier normalization for the RH Krein lane

Mathlib's real Fourier transform uses exp(-2*pi*i*x*xi), while the AEGIS
Krein numerics use angular frequency t in exp(i*t*x).  This file pins the
conversion xi = -t/(2*pi) and then identifies the Mellin transform of the
multiplicative autocorrelation on the critical line with the Fourier
norm-square of the logarithmic lift.

No sign theorem and no RH conclusion is asserted here.
-/

open MeasureTheory FourierTransform Complex
open scoped ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCriticalLineBridgeV1

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilPairedZeroEvaluationV9
open AEGIS.WeilAutocorrelationMellinV11

/-- Critical-line Mellin transform equals the Mathlib Fourier transform of the
unitary logarithmic lift at the scaled frequency -t/(2*pi). -/
theorem critical_mellin_eq_fourier_scaled_v1
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    mellin g.1 (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      𝓕 (logLift g.1) (-t / (2 * Real.pi)) := by
  rw [mellin_eq_log_integral_v9, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  unfold WeilLogMellinIntegrandV9 logLift
  simp only [smul_eq_mul]
  have hphase :
      -2 * Real.pi * u * (-t / (2 * Real.pi)) = t * u := by
    field_simp [Real.pi_ne_zero]
  rw [hphase]
  have hexp :
      Complex.exp
          ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) * (u : ℂ)) =
        Complex.exp (((t * u : ℝ) : ℂ) * I) *
          (Real.exp (u / 2) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- On the critical line the reflected Mellin factor is the same factor. -/
theorem critical_reflection_v1 (t : ℝ) :
    1 - conj ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
  apply Complex.ext <;> norm_num

/-- The actual repository multiplicative autocorrelation has critical-line
Mellin transform equal to the Fourier norm-square of the logarithmic lift,
with the exact Mathlib 2*pi frequency normalization exposed. -/
theorem autocorrelation_mellin_critical_normSq_v1
    (g : WeilCompactSmoothGV1) (t : ℝ) :
    mellin (WeilAutocorrelationV1 g)
        (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((Complex.normSq
        (𝓕 (logLift g.1) (-t / (2 * Real.pi))) : ℝ) : ℂ) := by
  rw [weil_autocorrelation_mellin_factorization_v11]
  rw [critical_reflection_v1 t]
  rw [critical_mellin_eq_fourier_scaled_v1]
  rw [Complex.mul_conj]

#print axioms AEGIS.RHKreinCriticalLineBridgeV1.critical_mellin_eq_fourier_scaled_v1
#print axioms AEGIS.RHKreinCriticalLineBridgeV1.autocorrelation_mellin_critical_normSq_v1

end AEGIS.RHKreinCriticalLineBridgeV1
