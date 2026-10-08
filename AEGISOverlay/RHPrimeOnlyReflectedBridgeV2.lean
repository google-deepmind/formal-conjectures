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

import RHPrimeOnlyGrowthBridgeV1
import WeilZeroKernelHermitianV11

/-!
# RH fixed-detector reflected prime bridge V2

Unlike the earlier direct-positive-shift remainder interface, the archived
identity K_g(-d) = -B(g, T_d g) pairs the positive arithmetic orbit with
**minus the negative-shift zero kernel**. The Hermitian identity transfers its
norm to the positive zero-kernel shift. No equality between K(d) and -K(-d)
is assumed.

This file proves the reflection/subexponential-growth equivalence and the
correctly-oriented terminal bridge to Mathlib's exact RiemannHypothesis.
The bounded remainder and prime-only growth premises are separately explicit;
neither is asserted unconditionally here.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeOnlyReflectedBridgeV2

open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.RHKernelSubexponentialV1
open AEGIS.RHSubexpBoundedPerturbationV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1

/-- The actual arithmetic orbit is compared with -K(-t), **not** K(t).
This is the orientation of the archived exact signed-prime / actual-B identity. -/
def ReflectedFixedKernelArithmeticRemainderBoundedV2 : Prop :=
  BoundedDifferenceOnNonnegativeV1
    (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t))
    (combinedArithmeticOrbitV1 detectingPacket)

/-- Hermitian reflection makes the reflected, sign-reversed kernel and the
positive-shift kernel have identical nonnegative-time growth bounds. -/
theorem reflected_kernel_subexponential_iff
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g) :
    SubexponentialAtTopV1
      (fun t : ℝ => -WeilZeroTranslationKernelV11 g (-t)) ↔
    PacketKernelSubexponentialV1 g := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro t ht
    have hb := hbound t ht
    change ‖-WeilZeroTranslationKernelV11 g (-t)‖ ≤
      C * Real.exp (ε * t) at hb
    simpa only [norm_neg, zero_translation_kernel_neg_eq_conj_v11 g t hm,
      Complex.norm_conj] using hb
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro t ht
    change ‖-WeilZeroTranslationKernelV11 g (-t)‖ ≤
      C * Real.exp (ε * t)
    rw [norm_neg, zero_translation_kernel_neg_eq_conj_v11 g t hm, Complex.norm_conj]
    exact hbound t ht

/-- Given exactly the corrected kernel/arithmetic bounded remainder, the
prime-only orbit has exponential type zero if and only if Mathlib RH holds.
Both sides refer to the same fixed moment-zero detecting packet. -/
theorem prime_only_subexponential_iff_rh_of_reflected_bridge
    (hBridge : ReflectedFixedKernelArithmeticRemainderBoundedV2) :
    SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket) ↔
      RiemannHypothesis := by
  constructor
  · intro hPrime
    have hArithmetic : SubexponentialAtTopV1
        (combinedArithmeticOrbitV1 detectingPacket) :=
      (combinedArithmetic_subexponential_iff_primeOnly_v1 detectingPacket).2 hPrime
    have hReflected : SubexponentialAtTopV1
        (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t)) :=
      subexponential_of_bounded_difference_v1
        (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t))
        (combinedArithmeticOrbitV1 detectingPacket) hArithmetic hBridge
    have hKernel : PacketKernelSubexponentialV1 detectingPacket :=
      (reflected_kernel_subexponential_iff detectingPacket detectingPacket_moments).mp
        hReflected
    exact (fixed_detecting_packet_subexponential_iff_rh).mp hKernel
  · intro hRH
    have hKernel : PacketKernelSubexponentialV1 detectingPacket :=
      (fixed_detecting_packet_subexponential_iff_rh).mpr hRH
    have hReflected : SubexponentialAtTopV1
        (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t)) :=
      (reflected_kernel_subexponential_iff detectingPacket detectingPacket_moments).mpr
        hKernel
    have hBridgeSymm : BoundedDifferenceOnNonnegativeV1
        (combinedArithmeticOrbitV1 detectingPacket)
        (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t)) :=
      boundedDifference_symm_v1 _ _ hBridge
    have hArithmetic : SubexponentialAtTopV1
        (combinedArithmeticOrbitV1 detectingPacket) :=
      subexponential_of_bounded_difference_v1
        (combinedArithmeticOrbitV1 detectingPacket)
        (fun t : ℝ => -WeilZeroTranslationKernelV11 detectingPacket (-t))
        hReflected hBridgeSymm
    exact (combinedArithmetic_subexponential_iff_primeOnly_v1 detectingPacket).mp
      hArithmetic

/-- Same corrected premises discharge the *exact* AEGIS universal gate,
without pretending that either remaining premise has been proved. -/
theorem universal_of_prime_only_growth_and_reflected_bridge
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : ReflectedFixedKernelArithmeticRemainderBoundedV2) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13
    ((prime_only_subexponential_iff_rh_of_reflected_bridge hBridge).mp hPrime)

end AEGIS.RHPrimeOnlyReflectedBridgeV2

#print axioms AEGIS.RHPrimeOnlyReflectedBridgeV2.reflected_kernel_subexponential_iff
#print axioms AEGIS.RHPrimeOnlyReflectedBridgeV2.prime_only_subexponential_iff_rh_of_reflected_bridge
#print axioms AEGIS.RHPrimeOnlyReflectedBridgeV2.universal_of_prime_only_growth_and_reflected_bridge
