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

import RHPrimeOnlyReflectedBridgeV2

/-!
# RH reflected arithmetic bridge: an eventual (tail-only) remainder suffices

The archived signed-prime/actual-B comparison holds on a separated-translation
tail, not on all t >= 0. The correct proof consumer needs precisely that tail:
continuity of the actual translated zero kernel controls the initial compact
interval, and subexponential arithmetic growth controls the remaining tail.

This removes any need for a globally uniform remainder bound or an a priori
local bound for the totalized arithmetic convolution. It does not prove the
arithmetic growth or the tail dictionary equality.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open Set Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimeOnlyReflectedTailV3

open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilZeroKernelHermitianV11
open AEGIS.RHZeroKernelLaplaceAnalyticV12
open AEGIS.RHFixedPacketFrontierV1
open AEGIS.RHKernelSubexponentialV1
open AEGIS.RHSubexpBoundedPerturbationV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1

/-- The exact eventual remainder needed by the source's signed-prime estimate:
positive arithmetic translation corresponds to -K(-t). -/
def EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3 : Prop :=
  ∃ T D : ℝ, 0 ≤ D ∧
    ∀ t : ℝ, T ≤ t →
      ‖-WeilZeroTranslationKernelV11 detectingPacket (-t) -
        combinedArithmeticOrbitV1 detectingPacket t‖ ≤ D

/-- Abstract tail transfer, using compactness of [0,max 0 T] to avoid
strengthening the arithmetic remainder to an all-shift estimate. -/
theorem kernel_subexponential_of_eventual_reflected_arithmetic
    (g : WeilCompactSmoothGV1) (hm : WeilMomentConditionsV1 g)
    (A : ℝ → ℂ) (hA : SubexponentialAtTopV1 A)
    (hBridge : ∃ T D : ℝ, 0 ≤ D ∧
      ∀ t : ℝ, T ≤ t →
        ‖-WeilZeroTranslationKernelV11 g (-t) - A t‖ ≤ D) :
    PacketKernelSubexponentialV1 g := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hA ε hε
  obtain ⟨T, D, hD0, hD⟩ := hBridge
  let R : ℝ := max 0 T
  have hTR : T ≤ R := le_max_right _ _
  have hcont :
      Continuous (fun t : ℝ => ‖WeilZeroTranslationKernelV11 g t‖) :=
    (zero_translation_kernel_continuous_v12 g).norm
  have hcompact :
      BddAbove ((fun t : ℝ => ‖WeilZeroTranslationKernelV11 g t‖) '' Icc (0 : ℝ) R) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn
  obtain ⟨M, hM⟩ := bddAbove_def.mp hcompact
  let B : ℝ := max 0 (max M (C + D))
  have hB0 : 0 ≤ B := le_max_left _ _
  have hMB : M ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hCDB : C + D ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB0, ?_⟩
  intro t ht0
  have hExp : 1 ≤ Real.exp (ε * t) :=
    Real.one_le_exp (mul_nonneg hε.le ht0)
  by_cases hsmall : t ≤ R
  · have hMbound : ‖WeilZeroTranslationKernelV11 g t‖ ≤ M :=
      hM _ ⟨t, ⟨ht0, hsmall⟩, rfl⟩
    calc
      ‖WeilZeroTranslationKernelV11 g t‖ ≤ B := hMbound.trans hMB
      _ = B * 1 := by ring
      _ ≤ B * Real.exp (ε * t) :=
        mul_le_mul_of_nonneg_left hExp hB0
  · have htR : R < t := lt_of_not_ge hsmall
    have htT : T ≤ t := hTR.trans htR.le
    have hnorm :
        ‖WeilZeroTranslationKernelV11 g t‖ =
          ‖-WeilZeroTranslationKernelV11 g (-t)‖ := by
      rw [norm_neg, zero_translation_kernel_neg_eq_conj_v11 g t hm, norm_conj]
    have htri :
        ‖-WeilZeroTranslationKernelV11 g (-t)‖ ≤
          ‖-WeilZeroTranslationKernelV11 g (-t) - A t‖ + ‖A t‖ := by
      simpa only [sub_add_cancel] using
        (norm_add_le
          (-WeilZeroTranslationKernelV11 g (-t) - A t) (A t))
    have hDexp : D ≤ D * Real.exp (ε * t) := by
      calc
        D = D * 1 := by ring
        _ ≤ D * Real.exp (ε * t) :=
          mul_le_mul_of_nonneg_left hExp hD0
    calc
      ‖WeilZeroTranslationKernelV11 g t‖ =
          ‖-WeilZeroTranslationKernelV11 g (-t)‖ := hnorm
      _ ≤ ‖-WeilZeroTranslationKernelV11 g (-t) - A t‖ + ‖A t‖ := htri
      _ ≤ D + C * Real.exp (ε * t) :=
        add_le_add (hD t htT) (hC t ht0)
      _ ≤ (C + D) * Real.exp (ε * t) := by
        calc
          D + C * Real.exp (ε * t) ≤
              D * Real.exp (ε * t) + C * Real.exp (ε * t) :=
            calc
              D + C * Real.exp (ε * t) =
                  C * Real.exp (ε * t) + D := by ring
              _ ≤ C * Real.exp (ε * t) + D * Real.exp (ε * t) :=
                add_le_add_right hDexp _
              _ = D * Real.exp (ε * t) + C * Real.exp (ε * t) := by ring
          _ = (C + D) * Real.exp (ε * t) := by ring
      _ ≤ B * Real.exp (ε * t) :=
        mul_le_mul_of_nonneg_right hCDB (Real.exp_nonneg _)

/-- Main consequence: only the tail bridge and the prime-only subexponential
growth estimate are needed; no uniform remainder at small t. -/
theorem riemannHypothesis_of_prime_only_growth_and_eventual_reflected_bridge
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3) :
    RiemannHypothesis := by
  have hArithmetic :
      SubexponentialAtTopV1 (combinedArithmeticOrbitV1 detectingPacket) :=
    (combinedArithmetic_subexponential_iff_primeOnly_v1 detectingPacket).2 hPrime
  have hKernel : PacketKernelSubexponentialV1 detectingPacket :=
    kernel_subexponential_of_eventual_reflected_arithmetic
      detectingPacket detectingPacket_moments
      (combinedArithmeticOrbitV1 detectingPacket) hArithmetic hBridge
  exact riemannHypothesis_of_fixed_detecting_packet_subexponential hKernel

/-- The same corrected tail-only hypotheses reach the official AEGIS
universal residual with no axiom and no change to the RH target. -/
theorem universal_of_prime_only_growth_and_eventual_reflected_bridge
    (hPrime : SubexponentialAtTopV1 (primeOnlyOrbitV1 detectingPacket))
    (hBridge : EventuallyReflectedFixedKernelArithmeticRemainderBoundedV3) :
    AEGIS.RHMillenniumGateV10.UniversalZeroQuadraticNonnegativeV10 :=
  AEGIS.WeilRHImpliesFinalSignV13.rh_implies_universal_v13
    (riemannHypothesis_of_prime_only_growth_and_eventual_reflected_bridge
      hPrime hBridge)

end AEGIS.RHPrimeOnlyReflectedTailV3

#print axioms AEGIS.RHPrimeOnlyReflectedTailV3.kernel_subexponential_of_eventual_reflected_arithmetic
#print axioms AEGIS.RHPrimeOnlyReflectedTailV3.riemannHypothesis_of_prime_only_growth_and_eventual_reflected_bridge
#print axioms AEGIS.RHPrimeOnlyReflectedTailV3.universal_of_prime_only_growth_and_eventual_reflected_bridge
