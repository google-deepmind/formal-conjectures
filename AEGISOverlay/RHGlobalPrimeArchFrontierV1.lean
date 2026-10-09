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

import RHKreinSymbolIntegrationV1
import RHRestrictedWeilBridgeV13

/-!
# Exact global prime versus Archimedean domination frontier

The actual critical-line gamma identity rewrites the universal sign as one
unconditional inequality between the actual prime sum and its Archimedean
Fourier integral. No approximation class or finite-window restriction is
introduced. The implication to Mathlib's RiemannHypothesis uses the existing
restricted Weil criterion and does not import a conjecture placeholder.
-/

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHGlobalPrimeArchFrontierV1

open AEGIS.RHKreinSymbolIntegrationV1
open AEGIS.WeilAutocorrelationExplicitFormulaV10
open AEGIS.RHMillenniumGateV10
open AEGIS.RHRestrictedWeilBridgeV13

/-- Global domination for exactly the original smooth moment-zero carrier. -/
def GlobalPrimeArchDomination : Prop :=
  ∀ g : WeilCompactSmoothGV1, WeilMomentConditionsV1 g →
    (WeilPrimeSumV1 (WeilAutocorrelationV1 g)).re ≤
      (1 / (4 * Real.pi)) *
        ∫ t : ℝ, archSymbol t * criticalSpectralMass g t

/-- The new unconditional critical-line identity yields an exact equivalence. -/
theorem global_prime_arch_iff_universal :
    GlobalPrimeArchDomination ↔ UniversalZeroQuadraticNonnegativeV10 := by
  constructor
  · intro h g hm
    apply (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mp
    rw [actual_arithmetic_real_eq_prime_sub_archSymbol]
    exact sub_nonpos.mpr (h g hm)
  · intro h g hm
    have hz := (autocorrelation_arithmetic_nonpositive_iff_zero_nonnegative_v10 g hm).mpr
      (h g hm)
    rw [actual_arithmetic_real_eq_prime_sub_archSymbol] at hz
    exact sub_nonpos.mp hz

/-- This explicit global inequality suffices for the actual Mathlib proposition. -/
theorem riemannHypothesis_of_global_prime_arch
    (h : GlobalPrimeArchDomination) : RiemannHypothesis :=
  restricted_weil_criterion_kernel_bridge_v13 (global_prime_arch_iff_universal.mp h)

end AEGIS.RHGlobalPrimeArchFrontierV1

#print axioms AEGIS.RHGlobalPrimeArchFrontierV1.global_prime_arch_iff_universal
#print axioms AEGIS.RHGlobalPrimeArchFrontierV1.riemannHypothesis_of_global_prime_arch
