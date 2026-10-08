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

import RHSignedPrimeChebyshevFiniteBridgeV6
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# AEGIS Ω: local arithmetic integrability of the genuine Chebyshev convolutions

This module attempts to discharge the integrability input to the already
defined exact signed-prime/Chebyshev V6 dictionary, using existing facts:
monotonicity of Chebyshev theta and psi; the continuous logarithmic lift;
compactly-supported smooth AEGIS discrepancy kernel.

SOURCE CANDIDATE: requires exact-head Lean compilation and axiom audit.
NO mathematical statement from earlier modules is changed.
-/

open Set MeasureTheory Complex Function
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSignedPrimeConvolutionIntegrabilityV7

open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHPrimePowerKernelConnectorV1
open AEGIS.RHPrimeDiscrepancyLogSubstitutionV4
open AEGIS.RHSignedPrimeActualKernelTailV5
open AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.WeilWidthArchCorrelationV25

private theorem theta_log_locally_integrable_v7 :
    LocallyIntegrable (fun y : ℝ => Chebyshev.theta (Real.exp y)) volume := by
  have hm : Monotone (fun y : ℝ => Chebyshev.theta (Real.exp y)) :=
    Chebyshev.theta_mono.comp Real.exp_strictMono.monotone
  exact hm.locallyIntegrable

private theorem psi_log_locally_integrable_v7 :
    LocallyIntegrable (fun y : ℝ => Chebyshev.psi (Real.exp y)) volume := by
  have hm : Monotone (fun y : ℝ => Chebyshev.psi (Real.exp y)) :=
    Chebyshev.psi_mono.comp Real.exp_strictMono.monotone
  exact hm.locallyIntegrable

private theorem complex_ofReal_locally_integrable_v7
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y : ℝ => (f y : ℂ)) volume := by
  apply locallyIntegrableOn_univ.mp
  have h := Complex.ofRealCLM.locallyIntegrableOn_comp
    (hf.locallyIntegrableOn Set.univ)
  simpa [Function.comp_def, Complex.ofRealCLM_apply] using h

/-- No prime-growth hypothesis: actual theta normalized discrepancy is locally integrable. -/
theorem normalized_prime_only_locally_integrable_v7 :
    LocallyIntegrable normalizedPrimeOnlyDiscrepancyComplexV1 volume := by
  have hdiff : LocallyIntegrable
      (fun y : ℝ => Chebyshev.theta (Real.exp y) - Real.exp y) volume :=
    (theta_log_locally_integrable_v7).sub Real.continuous_exp.locallyIntegrable
  have hf : Continuous (fun y : ℝ => Real.exp (-y / 2)) := by fun_prop
  have hreal : LocallyIntegrable
      (fun y : ℝ =>
        Real.exp (-y / 2) * (Chebyshev.theta (Real.exp y) - Real.exp y)) volume :=
    LocallyIntegrable.continuous_mul hf hdiff
  simpa [normalizedPrimeOnlyDiscrepancyComplexV1] using
    (complex_ofReal_locally_integrable_v7
      (fun y : ℝ =>
        Real.exp (-y / 2) * (Chebyshev.theta (Real.exp y) - Real.exp y)) hreal)

/-- The higher-prime-power normalized correction is locally integrable too. -/
theorem normalized_prime_powers_locally_integrable_v7 :
    LocallyIntegrable normalizedPrimePowerCorrectionComplexV1 volume := by
  have hdiff : LocallyIntegrable
      (fun y : ℝ =>
        Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y)) volume :=
    (psi_log_locally_integrable_v7).sub theta_log_locally_integrable_v7
  have hf : Continuous (fun y : ℝ => Real.exp (-y / 2)) := by fun_prop
  have hreal : LocallyIntegrable
      (fun y : ℝ =>
        Real.exp (-y / 2) *
          (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y))) volume :=
    LocallyIntegrable.continuous_mul hf hdiff
  simpa [normalizedPrimePowerCorrectionComplexV1] using
    (complex_ofReal_locally_integrable_v7
      (fun y : ℝ =>
        Real.exp (-y / 2) *
          (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y))) hreal)

/-- The exact discrepancy kernel has compact support, not just an L1 norm. -/
theorem discrepancy_kernel_hasCompactSupport_v7 (g : WeilCompactSmoothGV1) :
    HasCompactSupport (primeDiscrepancyKernelV1 g) := by
  have hs := logCorrelation_hasCompactSupport_connector_v1 g
  have hd : HasCompactSupport (deriv (logCorrelationV25 g)) := hs.deriv
  have hscale : HasCompactSupport
      (fun u : ℝ => logCorrelationV25 g u / (2 : ℂ)) := by
    change HasCompactSupport
      (logCorrelationV25 g * (fun _u : ℝ => (2 : ℂ)⁻¹))
    exact hs.mul_right
  change HasCompactSupport
    (deriv (logCorrelationV25 g) +
      (fun u : ℝ => logCorrelationV25 g u / (2 : ℂ)))
  exact hd.add hscale

private theorem discrepancy_kernel_continuous_v7 (g : WeilCompactSmoothGV1) :
    Continuous (primeDiscrepancyKernelV1 g) := by
  have hc := logCorrelation_contDiff_connector_v1 g
  have hd : Continuous (deriv (logCorrelationV25 g)) :=
    hc.continuous_deriv (by simp)
  have hb : Continuous (fun u : ℝ => logCorrelationV25 g u / (2 : ℂ)) :=
    hc.continuous.div_const 2
  change Continuous
    (deriv (logCorrelationV25 g) +
      (fun u : ℝ => logCorrelationV25 g u / (2 : ℂ)))
  exact hd.add hb

/-- Both arithmetic convolutions have honest Bochner integrals at every shift. -/
theorem arithmetic_convolutions_integrable_v7
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    Integrable (fun y : ℝ =>
      primeDiscrepancyKernelV1 g (d - y) *
        normalizedPrimeOnlyDiscrepancyComplexV1 y) volume ∧
    Integrable (fun y : ℝ =>
      primeDiscrepancyKernelV1 g (d - y) *
        normalizedPrimePowerCorrectionComplexV1 y) volume := by
  have hc := discrepancy_kernel_hasCompactSupport_v7 g
  have hcont := discrepancy_kernel_continuous_v7 g
  have hPrime := hc.convolutionExists_left
    (ContinuousLinearMap.mul ℝ ℂ) hcont
    normalized_prime_only_locally_integrable_v7
  have hPower := hc.convolutionExists_left
    (ContinuousLinearMap.mul ℝ ℂ) hcont
    normalized_prime_powers_locally_integrable_v7
  constructor
  · simpa only [ContinuousLinearMap.mul_apply'] using
      (hPrime d).integrable_swap
  · simpa only [ContinuousLinearMap.mul_apply'] using
      (hPower d).integrable_swap

/-- Supplies the V6 integrability target with no hypothesis, even without eventual shift cutoff. -/
theorem eventual_arithmetic_convolutions_integrable_v7 :
    EventuallyArithmeticConvolutionsIntegrableV6 := by
  refine ⟨0, ?_⟩
  intro d _hd
  exact arithmetic_convolutions_integrable_v7 detectingPacket d

/-- With integrability supplied, only the explicitly named interval-extension input remains
    to close the actual signed-prime/Chebyshev dictionary. -/
theorem eventual_signed_dictionary_of_interval_extension_v7
    (hExtend : EventuallyChebyshevFiniteIntegralExtendsV6) :
    EventuallySignedPrimeEqualsCombinedOrbitV5 :=
  eventual_signed_prime_equals_combined_of_analytic_closure
    hExtend eventual_arithmetic_convolutions_integrable_v7

end AEGIS.RHSignedPrimeConvolutionIntegrabilityV7

#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.normalized_prime_only_locally_integrable_v7
#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.normalized_prime_powers_locally_integrable_v7
#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.discrepancy_kernel_hasCompactSupport_v7
#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.arithmetic_convolutions_integrable_v7
#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.eventual_arithmetic_convolutions_integrable_v7
#print axioms AEGIS.RHSignedPrimeConvolutionIntegrabilityV7.eventual_signed_dictionary_of_interval_extension_v7
