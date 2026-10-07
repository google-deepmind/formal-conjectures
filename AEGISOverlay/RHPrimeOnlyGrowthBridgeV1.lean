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

import AEGISOverlay.RHPrimePowerKernelConnectorV1
import RHSubexpBoundedPerturbationV1
import RHKernelSubexponentialV1
import RHGlobalPrimeArchFrontierV1

/-!
# Prime-only growth: exact connection between the independent RH lanes

This module joins existing independently developed source:
* PR #59: the actual compact prime-discrepancy kernel, and a proved
  **uniformly bounded** higher-prime-power convolution;
* PR #60: invariance of subexponential growth under bounded perturbations;
* PR #56: the fixed detecting zero kernel's subexponential criterion for RH.

The prime-only normalized discrepancy is explicitly
  exp(-y/2) (theta(exp(y)) - exp(y)).
The full normalized Chebyshev discrepancy is
  exp(-y/2) (psi(exp(y)) - exp(y)).
Their exact decomposition is checked algebraically below.

The derived combined arithmetic orbit differs from the prime-only orbit by
the unconditionally bounded higher-prime-power contribution. Consequently,
both orbits have **equivalent** subexponential growth.

Connecting either orbit to the canonical zero-translation kernel requires
a separate analytic identity or a bounded-remainder estimate. Neither
that estimate nor the prime-only subexponential estimate is assumed to
have been proved. Both obligations are explicit inputs of the terminal.

Note: integration in Lean is totalized. To interpret these orbit integrals
analytically, integrability must be established in the source representation;
the terminal never silently assumes such an analytic identification.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeOnlyGrowthBridgeV1

open AEGIS.RHPrimePowerKernelConnectorV1
open AEGIS.RHSubexpBoundedPerturbationV1
open AEGIS.RHKernelSubexponentialV1
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.WeilZeroTwoPointV11

/-- The actual prime-only logarithmic discrepancy, with RH normalization. -/
def normalizedPrimeOnlyDiscrepancyComplexV1 (y : ℝ) : ℂ :=
  ((Real.exp (-y / 2) *
      (Chebyshev.theta (Real.exp y) - Real.exp y) : ℝ) : ℂ)

/-- The complete normalized Chebyshev psi discrepancy. -/
def normalizedFullPrimeDiscrepancyComplexV1 (y : ℝ) : ℂ :=
  ((Real.exp (-y / 2) *
      (Chebyshev.psi (Real.exp y) - Real.exp y) : ℝ) : ℂ)

/-- Exact decomposition at each logarithmic argument, with no growth
hypothesis and no positivity hypothesis. -/
theorem normalizedFull_eq_primeOnly_add_primePowers_v1 (y : ℝ) :
    normalizedFullPrimeDiscrepancyComplexV1 y =
      normalizedPrimeOnlyDiscrepancyComplexV1 y +
        normalizedPrimePowerCorrectionComplexV1 y := by
  unfold normalizedFullPrimeDiscrepancyComplexV1
    normalizedPrimeOnlyDiscrepancyComplexV1
    normalizedPrimePowerCorrectionComplexV1
  have heq :
      Chebyshev.psi (Real.exp y) - Real.exp y =
        (Chebyshev.theta (Real.exp y) - Real.exp y) +
          (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y)) := by
    ring
  rw [heq, mul_add, Complex.ofReal_add]

/-- Convolution of the actual compact AEGIS discrepancy kernel with the
prime-only normalized Chebyshev theta error. -/
def primeOnlyOrbitV1 (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∫ y : ℝ, primeDiscrepancyKernelV1 g (d - y) *
    normalizedPrimeOnlyDiscrepancyComplexV1 y ∂volume

/-- The same actual kernel convolved with the higher-prime-power error. -/
def higherPrimePowerOrbitV1 (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∫ y : ℝ, primeDiscrepancyKernelV1 g (d - y) *
    normalizedPrimePowerCorrectionComplexV1 y ∂volume

/-- Direct convolution with the complete normalized Chebyshev psi
discrepancy, independently of how the integral is decomposed. -/
def fullPrimeDiscrepancyOrbitV1 (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  ∫ y : ℝ, primeDiscrepancyKernelV1 g (d - y) *
    normalizedFullPrimeDiscrepancyComplexV1 y ∂volume

/-- The arithmetic orbit assembled from the prime-only and prime-power
parts. No unproved interchange of integration and summation is invoked. -/
def combinedArithmeticOrbitV1 (g : WeilCompactSmoothGV1) (d : ℝ) : ℂ :=
  primeOnlyOrbitV1 g d + higherPrimePowerOrbitV1 g d

/-- This is the missing exact connection to the actual full psi convolution.
The two integrability hypotheses are explicit, rather than silently
distributing a nonintegrable totalized Bochner integral. -/
theorem fullPrimeDiscrepancyOrbit_eq_combined_of_integrable_v1
    (g : WeilCompactSmoothGV1) (d : ℝ)
    (hPrime : Integrable
      (fun y : ℝ =>
        primeDiscrepancyKernelV1 g (d - y) *
          normalizedPrimeOnlyDiscrepancyComplexV1 y) volume)
    (hPowers : Integrable
      (fun y : ℝ =>
        primeDiscrepancyKernelV1 g (d - y) *
          normalizedPrimePowerCorrectionComplexV1 y) volume) :
    fullPrimeDiscrepancyOrbitV1 g d = combinedArithmeticOrbitV1 g d := by
  have hpoint :
      (fun y : ℝ => primeDiscrepancyKernelV1 g (d - y) *
        normalizedFullPrimeDiscrepancyComplexV1 y) =
      (fun y : ℝ =>
        primeDiscrepancyKernelV1 g (d - y) *
          normalizedPrimeOnlyDiscrepancyComplexV1 y +
        primeDiscrepancyKernelV1 g (d - y) *
          normalizedPrimePowerCorrectionComplexV1 y) := by
    funext y
    rw [normalizedFull_eq_primeOnly_add_primePowers_v1]
    ring
  unfold fullPrimeDiscrepancyOrbitV1
  rw [hpoint, integral_add hPrime hPowers]
  rfl

/-- The full arithmetic orbit differs from the genuine prime-only
convolution by a uniformly bounded function. -/
theorem combinedArithmetic_boundedDifference_primeOnly_v1
    (g : WeilCompactSmoothGV1) :
    BoundedDifferenceOnNonnegativeV1
      (combinedArithmeticOrbitV1 g) (primeOnlyOrbitV1 g) := by
  obtain ⟨C, hC0, hC⟩ := higherPrimePowerContribution_bounded_v1 g
  refine ⟨C, hC0, ?_⟩
  intro d _hd
  calc
    ‖combinedArithmeticOrbitV1 g d - primeOnlyOrbitV1 g d‖ =
        ‖higherPrimePowerOrbitV1 g d‖ := by
      congr 1
      dsimp only [combinedArithmeticOrbitV1]
      abel
    _ ≤ C := hC d

/-- An unconditional transfer of exponential type zero between the
two actually defined arithmetic orbits. -/
theorem combinedArithmetic_subexponential_iff_primeOnly_v1
    (g : WeilCompactSmoothGV1) :
    SubexponentialAtTopV1 (combinedArithmeticOrbitV1 g) ↔
      SubexponentialAtTopV1 (primeOnlyOrbitV1 g) :=
  subexponential_iff_of_bounded_difference_v1
    (combinedArithmeticOrbitV1 g) (primeOnlyOrbitV1 g)
    (combinedArithmetic_boundedDifference_primeOnly_v1 g)

/-- The independent analytic link still needed: the canonical zero
kernel differs from the combined Chebyshev arithmetic orbit by
a uniformly bounded remainder on the positive half-line. -/
def FixedKernelArithmeticRemainderBoundedV1 : Prop :=
  BoundedDifferenceOnNonnegativeV1
    (fun t : ℝ => WeilZeroTranslationKernelV11 detectingPacket t)
    (combinedArithmeticOrbitV1 detectingPacket)

/-- Precise terminal: subexponential prime-only arithmetic growth AND
the zero-kernel arithmetic identification modulo a bounded term imply
Mathlib's exact RH proposition, without any new axiom. These inputs
are not supplied by the existing modules. -/
theorem riemannHypothesis_of_primeOnly_growth_and_kernel_bridge_v1
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : FixedKernelArithmeticRemainderBoundedV1) :
    RiemannHypothesis := by
  have hArithmetic : SubexponentialAtTopV1
      (combinedArithmeticOrbitV1 detectingPacket) :=
    (combinedArithmetic_subexponential_iff_primeOnly_v1 detectingPacket).2 hPrime
  have hKernel : SubexponentialAtTopV1
      (fun t : ℝ => WeilZeroTranslationKernelV11 detectingPacket t) :=
    subexponential_of_bounded_difference_v1
      (fun t : ℝ => WeilZeroTranslationKernelV11 detectingPacket t)
      (combinedArithmeticOrbitV1 detectingPacket)
      hArithmetic hBridge
  exact riemannHypothesis_of_fixed_detecting_packet_subexponential hKernel

/-- The same two analytic premises produce the *exact* universal residual
consumed by the official RH theorem in PR #13.  This uses the existing
kernel-checked RH => universal implication; it does not discharge either
prime-only growth or kernel-arithmetic remainder boundedness. -/
theorem universal_of_primeOnly_growth_and_kernel_bridge_v1
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : FixedKernelArithmeticRemainderBoundedV1) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13
    (riemannHypothesis_of_primeOnly_growth_and_kernel_bridge_v1 hPrime hBridge)

/-- The existing PR #51 global prime/Archimedean criterion is also reached,
with the *same* two explicit assumptions and no new analytic claim. -/
theorem globalPrimeArch_of_primeOnly_growth_and_kernel_bridge_v1
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : FixedKernelArithmeticRemainderBoundedV1) :
    AEGIS.RHGlobalPrimeArchFrontierV1.GlobalPrimeArchDomination :=
  (AEGIS.RHGlobalPrimeArchFrontierV1.global_prime_arch_iff_universal).mpr
    (universal_of_primeOnly_growth_and_kernel_bridge_v1 hPrime hBridge)

#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.normalizedFull_eq_primeOnly_add_primePowers_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.fullPrimeDiscrepancyOrbit_eq_combined_of_integrable_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.combinedArithmetic_boundedDifference_primeOnly_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.combinedArithmetic_subexponential_iff_primeOnly_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.riemannHypothesis_of_primeOnly_growth_and_kernel_bridge_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.universal_of_primeOnly_growth_and_kernel_bridge_v1
#print axioms AEGIS.RHPrimeOnlyGrowthBridgeV1.globalPrimeArch_of_primeOnly_growth_and_kernel_bridge_v1

end AEGIS.RHPrimeOnlyGrowthBridgeV1
