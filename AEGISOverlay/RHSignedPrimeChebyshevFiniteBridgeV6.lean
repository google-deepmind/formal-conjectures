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

import RHSignedPrimeActualKernelTailV5
import RHPrimeDiscrepancyLogSubstitutionV4
import WeilPrimeDiscrepancyEstimateV1

/-!
# Exact finite Abel-to-Chebyshev convolution bridge

The already-verified archived Abel source gives a finite integral. The already-
verified archived derivative identity identifies its integrand with the genuine
Chebyshev psi discrepancy and the existing V4 kernel. No growth hypothesis and
no invented representation are needed for this finite-window result.

This **does not** yet identify the truncated x-integral with the full positive
x-integral. Nor does it discharge the two existing integrability hypotheses of
`fullPrimeDiscrepancyOrbit_eq_combined_of_integrable_v1`.

This is a SOURCE CANDIDATE, not a current-head Lean replay receipt.
RH_PROVEN_UNCONDITIONALLY = false.
AUTHORITY_EFFECT = NONE.
-/

open Set Function MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6

open AEGIS.WeilPrimeAbelReductionV1
open AEGIS.WeilPrimeDiscrepancyV1
open AEGIS.WeilPrimeDiscrepancyEstimateV1
open AEGIS.WeilSignedKernelReductionV1
open AEGIS.RHPrimePowerKernelConnectorV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHPrimeDiscrepancyLogSubstitutionV4
open AEGIS.RHSignedPrimeActualKernelTailV5

/-- The integrand produced by the actual Abel derivative is precisely the
actual compact discrepancy kernel convolved against Mathlib's Chebyshev psi. -/
theorem neg_abel_integrand_eq_chebyshev_integrand
    (g : WeilCompactSmoothGV1) (d x : ℝ) (hx : 0 < x) :
    -(deriv (PrimeWeightV1 g d) x * PrimeDiscrepancyV1 x) =
      primeDiscrepancyKernelV1 g (d - Real.log x) *
        (((Real.exp (-Real.log x / 2) *
            (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ) := by
  rw [primeWeight_deriv_v1 g d x hx, discrepancy_eq_mathlib_v1 x]
  simp only [primeDiscrepancyKernelV1, Complex.ofReal_mul]
  ring

/-- Reconstructs the real, finite Abel integral with the exact normalized
Chebyshev discrepancy integrand; all stated hypotheses come from the actual
archive and the original packet moment condition. -/
theorem signed_prime_eq_finite_chebyshev_convolution
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    ∃ L : ℝ, 0 < L ∧ ∀ d : ℝ, 2 * L < d →
      ∃ N : ℕ, 1 ≤ N ∧
        (∀ x : ℝ, (N : ℝ) ≤ x → PrimeWeightV1 g d x = 0) ∧
        SignedPrimeCorrelationV1 g d =
          ∫ x in Ioc (1 : ℝ) (N : ℝ),
            primeDiscrepancyKernelV1 g (d - Real.log x) *
              (((Real.exp (-Real.log x / 2) *
                  (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ) := by
  obtain ⟨L, hL, hS⟩ := prime_correlation_discrepancy_v1 g hm
  refine ⟨L, hL, ?_⟩
  intro d hd
  obtain ⟨N, hN, hupper, hAbel⟩ := hS d hd
  refine ⟨N, hN, hupper, ?_⟩
  rw [hAbel]
  calc
    -(∫ x in Ioc (1 : ℝ) (N : ℝ),
        deriv (PrimeWeightV1 g d) x * PrimeDiscrepancyV1 x) =
        ∫ x in Ioc (1 : ℝ) (N : ℝ),
          -(deriv (PrimeWeightV1 g d) x * PrimeDiscrepancyV1 x) := by
            rw [integral_neg]
    _ = ∫ x in Ioc (1 : ℝ) (N : ℝ),
          primeDiscrepancyKernelV1 g (d - Real.log x) *
            (((Real.exp (-Real.log x / 2) *
                (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact neg_abel_integrand_eq_chebyshev_integrand g d x
        (lt_trans zero_lt_one hx.1)

/-! ### Exact residual interfaces: no unproved statement promoted to a fact -/

/-- The only missing interval-extension equation. The archived Abel theorem
provides some cutoff `N` on each large translation. The equality here must
follow from the actual compact support and a.e. disappearance of the derivative
outside `(1,N]`, rather than being silently assumed by integral totalization. -/
def EventuallyChebyshevFiniteIntegralExtendsV6 : Prop :=
  ∃ T : ℝ, ∀ (d : ℝ), T ≤ d → ∀ (N : ℕ), 1 ≤ N →
    (∀ x : ℝ, (N : ℝ) ≤ x → PrimeWeightV1 detectingPacket d x = 0) →
    (∫ x in Ioc (1 : ℝ) (N : ℝ),
      primeDiscrepancyKernelV1 detectingPacket (d - Real.log x) *
        (((Real.exp (-Real.log x / 2) *
            (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ)) =
    (∫ x in Ioi (0 : ℝ),
      primeDiscrepancyKernelV1 detectingPacket (d - Real.log x) *
        (((Real.exp (-Real.log x / 2) *
            (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ))

/-- The exact analytic integrability needed to split the full psi orbit into
prime-only and higher-prime-power convolutions. A proof should use the compact
support of `primeDiscrepancyKernelV1` and the local integrability of the genuine
Mathlib theta/psi step functions. -/
def EventuallyArithmeticConvolutionsIntegrableV6 : Prop :=
  ∃ T : ℝ, ∀ d : ℝ, T ≤ d →
    Integrable (fun y : ℝ =>
      primeDiscrepancyKernelV1 detectingPacket (d - y) *
        normalizedPrimeOnlyDiscrepancyComplexV1 y) volume ∧
    Integrable (fun y : ℝ =>
      primeDiscrepancyKernelV1 detectingPacket (d - y) *
        normalizedPrimePowerCorrectionComplexV1 y) volume

/-- All *already-proved* pieces compose, without changing the statement of the
V5 dictionary. The exact remaining hypotheses are ONLY interval extension and
the two Bochner integrability conditions stated above, not RH or growth. -/
theorem eventual_signed_prime_equals_combined_of_analytic_closure
    (hExtend : EventuallyChebyshevFiniteIntegralExtendsV6)
    (hIntegrable : EventuallyArithmeticConvolutionsIntegrableV6) :
    EventuallySignedPrimeEqualsCombinedOrbitV5 := by
  obtain ⟨L, hL, hFinite⟩ :=
    signed_prime_eq_finite_chebyshev_convolution
      detectingPacket detectingPacket_moments
  obtain ⟨T₁, hExtend'⟩ := hExtend
  obtain ⟨T₂, hIntegrable'⟩ := hIntegrable
  unfold EventuallySignedPrimeEqualsCombinedOrbitV5
  refine ⟨max (2 * L + 1) (max T₁ T₂), ?_⟩
  intro d hd
  have hdL : 2 * L < d := by
    have h := (le_max_left (2 * L + 1) (max T₁ T₂)).trans hd
    linarith
  have hdT₁ : T₁ ≤ d :=
    (le_max_left T₁ T₂).trans
      ((le_max_right (2 * L + 1) (max T₁ T₂)).trans hd)
  have hdT₂ : T₂ ≤ d :=
    (le_max_right T₁ T₂).trans
      ((le_max_right (2 * L + 1) (max T₁ T₂)).trans hd)
  obtain ⟨N, hN, hUpper, hFiniteEq⟩ := hFinite d hdL
  obtain ⟨hPrime, hPowers⟩ := hIntegrable' d hdT₂
  calc
    SignedPrimeCorrelationV1 detectingPacket d =
        ∫ x in Ioc (1 : ℝ) (N : ℝ),
          primeDiscrepancyKernelV1 detectingPacket (d - Real.log x) *
            (((Real.exp (-Real.log x / 2) *
                (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ) := hFiniteEq
    _ = ∫ x in Ioi (0 : ℝ),
          primeDiscrepancyKernelV1 detectingPacket (d - Real.log x) *
            (((Real.exp (-Real.log x / 2) *
                (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ) :=
          hExtend' d hdT₁ N hN hUpper
    _ = fullPrimeDiscrepancyOrbitV1 detectingPacket d :=
          (full_prime_discrepancy_orbit_eq_chebyshev_x_integral
            detectingPacket d).symm
    _ = combinedArithmeticOrbitV1 detectingPacket d :=
          fullPrimeDiscrepancyOrbit_eq_combined_of_integrable_v1
            detectingPacket d hPrime hPowers

end AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6

#print axioms AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.neg_abel_integrand_eq_chebyshev_integrand
#print axioms AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.signed_prime_eq_finite_chebyshev_convolution
#print axioms AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6.eventual_signed_prime_equals_combined_of_analytic_closure
