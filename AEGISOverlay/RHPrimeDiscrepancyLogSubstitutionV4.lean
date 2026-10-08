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

import RHPrimeOnlyReflectedTailV3
import WeilThreeBlockTranslatedPacketsV22

/-!
# Exact logarithmic substitution in the actual Chebyshev discrepancy orbit

This module reuses the pinned AEGIS integral-exp change of variables,
without any growth/sign hypothesis and without a non-measurable shadow
representation. The resulting x-integral is exactly the one needed to
connect the archived signed-prime Abel identity and weight derivative
to the current prime-only/prime-power arithmetic orbit.

The separate task of replacing the archived finite Abel interval
by its full positive-domain integral (using actual compact support),
and replaying that archive at the current pin, remains explicit.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open Set MeasureTheory Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeDiscrepancyLogSubstitutionV4

open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHPrimePowerKernelConnectorV1
open AEGIS.WeilThreeBlockTranslatedPacketsV22

/-- Exact exponential change of variables for a general complex convolution
integrand. The 1/x Jacobian is cancelled by dx = exp(y) dy. -/
theorem integral_log_convolution_eq_real_convolution
    (k P : ℝ → ℂ) (d : ℝ) :
    (∫ x in Ioi (0 : ℝ),
      k (d - Real.log x) * P (Real.log x) / (x : ℂ)) =
    ∫ y : ℝ, k (d - y) * P y := by
  rw [integral_exp_substitution_complex]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Real.log_exp, Complex.real_smul]
  have hx : (Real.exp y : ℂ) ≠ 0 := by simp
  field_simp

/-- Substituting the actual compact discrepancy kernel and complete normalized
Chebyshev psi discrepancy gives the exact positive-x representation. -/
theorem full_prime_discrepancy_orbit_eq_log_integral
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    fullPrimeDiscrepancyOrbitV1 g d =
      ∫ x in Ioi (0 : ℝ),
        primeDiscrepancyKernelV1 g (d - Real.log x) *
        normalizedFullPrimeDiscrepancyComplexV1 (Real.log x) / (x : ℂ) := by
  simpa only [fullPrimeDiscrepancyOrbitV1] using
    (integral_log_convolution_eq_real_convolution
      (primeDiscrepancyKernelV1 g)
      normalizedFullPrimeDiscrepancyComplexV1 d).symm

/-- The normalized full discrepancy evaluated at log(x) is Mathlib's actual
Chebyshev psi minus the continuum x, with no change of the arithmetic object. -/
theorem normalized_full_discrepancy_log
    (x : ℝ) (hx : 0 < x) :
    normalizedFullPrimeDiscrepancyComplexV1 (Real.log x) =
      ((Real.exp (-Real.log x / 2) * (Chebyshev.psi x - x) : ℝ) : ℂ) := by
  simp [normalizedFullPrimeDiscrepancyComplexV1, Real.exp_log hx]

/-- The precise integral appearing after the archived Abel reduction and
primeWeight derivative calculation. No prime growth bound is used here. -/
theorem full_prime_discrepancy_orbit_eq_chebyshev_x_integral
    (g : WeilCompactSmoothGV1) (d : ℝ) :
    fullPrimeDiscrepancyOrbitV1 g d =
      ∫ x in Ioi (0 : ℝ),
        primeDiscrepancyKernelV1 g (d - Real.log x) *
        (((Real.exp (-Real.log x / 2) *
            (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ)) := by
  rw [full_prime_discrepancy_orbit_eq_log_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [normalized_full_discrepancy_log x hx]
  simp only [div_eq_mul_inv, mul_assoc]

end AEGIS.RHPrimeDiscrepancyLogSubstitutionV4

#print axioms AEGIS.RHPrimeDiscrepancyLogSubstitutionV4.integral_log_convolution_eq_real_convolution
#print axioms AEGIS.RHPrimeDiscrepancyLogSubstitutionV4.full_prime_discrepancy_orbit_eq_log_integral
#print axioms AEGIS.RHPrimeDiscrepancyLogSubstitutionV4.normalized_full_discrepancy_log
#print axioms AEGIS.RHPrimeDiscrepancyLogSubstitutionV4.full_prime_discrepancy_orbit_eq_chebyshev_x_integral
