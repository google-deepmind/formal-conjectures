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

import AEGISOverlay.RHPrimePowerBoundedV1
import AEGISOverlay.RHBoundedConvolutionV1
import WeilWidthArchCorrelationV25
import WeilAutocorrelationClosureV1
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Convolution

/-!
# Higher prime powers are a bounded contribution to the AEGIS discrepancy orbit

For the actual logarithmic autocorrelation

  C_g(u) = logCorrelationV25 g u,

set

  kappa_g(u) = C_g'(u) + C_g(u)/2.

The current AEGIS source already identifies C_g with a smooth multiplicative
autocorrelation.  We prove here that C_g and its derivative have compact
support, hence kappa_g is L1.  Combining this with the unconditional Mathlib
bound psi(x)-theta(x)=O(sqrt x), formalized in RHPrimePowerBoundedV1, and the
generic L1 convolution estimate from RHBoundedConvolutionV1 shows that the
entire higher-prime-power part contributes only a translation-uniform bounded
term.

The remaining unbounded-growth question is therefore the prime-only
normalized discrepancy theta(exp y)-exp y.  No bound for that term and no RH
proof is asserted here.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open Set Filter Function MeasureTheory Complex
open scoped ContDiff

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimePowerKernelConnectorV1

open AEGIS.WeilWidthArchCorrelationV25

/-- Current-source smoothness of the logarithmic autocorrelation. -/
theorem logCorrelation_contDiff_connector_v1 (g : WeilCompactSmoothGV1) :
    ContDiff ℝ ∞ (logCorrelationV25 g) := by
  have heq : logCorrelationV25 g = fun u : ℝ =>
      (Real.exp (u / 2) : ℂ) * WeilAutocorrelationV1 g (Real.exp u) := by
    funext u
    exact logCorrelation_eq_autocorrelation_v25 g u
  rw [heq]
  exact ((Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_id.div_const 2))).mul
      ((_root_.weil_autocorrelation_contDiff_v1 g).comp
        Real.contDiff_exp))

/-- The logarithmic autocorrelation has compact support because the actual
multiplicative autocorrelation has compact positive support and log is
continuous there. -/
theorem logCorrelation_hasCompactSupport_connector_v1
    (g : WeilCompactSmoothGV1) :
    HasCompactSupport (logCorrelationV25 g) := by
  let K : Set ℝ := Real.log '' tsupport (WeilAutocorrelationV1 g)
  have hK : IsCompact K := by
    have hlog : ContinuousOn Real.log (tsupport (WeilAutocorrelationV1 g)) := by
      intro x hx
      have hxpos : 0 < x :=
        _root_.weil_autocorrelation_tsupport_positive_v1 g hx
      exact (Real.continuousAt_log (ne_of_gt hxpos)).continuousWithinAt
    exact
      (_root_.weil_autocorrelation_hasCompactSupport_v1 g).image_of_continuousOn hlog
  apply HasCompactSupport.of_support_subset_isCompact hK
  intro u hu
  have hA : WeilAutocorrelationV1 g (Real.exp u) ≠ 0 := by
    intro hz
    apply hu
    rw [logCorrelation_eq_autocorrelation_v25 g u, hz, mul_zero]
  have hm : Real.exp u ∈ tsupport (WeilAutocorrelationV1 g) :=
    subset_tsupport _ hA
  exact ⟨Real.exp u, hm, Real.log_exp u⟩

/-- The compact discrepancy kernel appearing after the logarithmic change of
variables. -/
def primeDiscrepancyKernelV1 (g : WeilCompactSmoothGV1) (u : ℝ) : ℂ :=
  deriv (logCorrelationV25 g) u + logCorrelationV25 g u / 2

/-- The actual compact discrepancy kernel is L1. -/
theorem primeDiscrepancyKernel_integrable_v1 (g : WeilCompactSmoothGV1) :
    Integrable (primeDiscrepancyKernelV1 g) volume := by
  have hc := logCorrelation_contDiff_connector_v1 g
  have hs := logCorrelation_hasCompactSupport_connector_v1 g
  have hd : Integrable (deriv (logCorrelationV25 g)) volume :=
    (hc.continuous_deriv (by simp)).integrable_of_hasCompactSupport hs.deriv
  have hb : Integrable (logCorrelationV25 g) volume :=
    hc.continuous.integrable_of_hasCompactSupport hs
  unfold primeDiscrepancyKernelV1
  exact hd.add (hb.div_const 2)

/-- Complex-valued version of the normalized higher-prime-power discrepancy. -/
def normalizedPrimePowerCorrectionComplexV1 (y : ℝ) : ℂ :=
  ((Real.exp (-y / 2) *
    (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y)) : ℝ) : ℂ)

/-- The normalized higher-prime-power discrepancy is uniformly bounded in
complex norm. -/
theorem normalizedPrimePowerCorrectionComplex_bounded_v1 :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      ‖normalizedPrimePowerCorrectionComplexV1 y‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    AEGIS.RHPrimePowerBoundedV1.normalized_prime_power_correction_bounded_v1
  refine ⟨B, hB, ?_⟩
  intro y
  change ‖((Real.exp (-y / 2) *
    (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y)) : ℝ) : ℂ)‖ ≤ B
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hbound y

/-- Higher prime powers contribute only a uniformly bounded term after
convolution with the actual AEGIS compact discrepancy kernel. -/
theorem higherPrimePowerContribution_bounded_v1
    (g : WeilCompactSmoothGV1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ,
      ‖∫ y : ℝ,
          primeDiscrepancyKernelV1 g (d - y) *
            normalizedPrimePowerCorrectionComplexV1 y ∂volume‖ ≤ C := by
  obtain ⟨B, hB, hP⟩ := normalizedPrimePowerCorrectionComplex_bounded_v1
  let L : ℝ := ∫ u : ℝ, ‖primeDiscrepancyKernelV1 g u‖ ∂volume
  have hL : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg fun u => norm_nonneg _
  refine ⟨B * L, mul_nonneg hB hL, ?_⟩
  intro d
  have hk := primeDiscrepancyKernel_integrable_v1 g
  have hgeneric :=
    AEGIS.RHBoundedConvolutionV1.norm_integral_mul_shift_le_v1
      volume (primeDiscrepancyKernelV1 g)
      normalizedPrimePowerCorrectionComplexV1 B d hk hP
  have hswap :
      (∫ y : ℝ,
          primeDiscrepancyKernelV1 g (d - y) *
            normalizedPrimePowerCorrectionComplexV1 y ∂volume) =
      ∫ u : ℝ,
          primeDiscrepancyKernelV1 g u *
            normalizedPrimePowerCorrectionComplexV1 (d - u) ∂volume := by
    simpa only [sub_sub_self] using
      (integral_sub_left_eq_self
        (fun u : ℝ =>
          primeDiscrepancyKernelV1 g u *
            normalizedPrimePowerCorrectionComplexV1 (d - u)) volume d)
  rw [hswap]
  simpa [L] using hgeneric

#print axioms AEGIS.RHPrimePowerKernelConnectorV1.logCorrelation_contDiff_connector_v1
#print axioms AEGIS.RHPrimePowerKernelConnectorV1.logCorrelation_hasCompactSupport_connector_v1
#print axioms AEGIS.RHPrimePowerKernelConnectorV1.primeDiscrepancyKernel_integrable_v1
#print axioms AEGIS.RHPrimePowerKernelConnectorV1.normalizedPrimePowerCorrectionComplex_bounded_v1
#print axioms AEGIS.RHPrimePowerKernelConnectorV1.higherPrimePowerContribution_bounded_v1

end AEGIS.RHPrimePowerKernelConnectorV1
