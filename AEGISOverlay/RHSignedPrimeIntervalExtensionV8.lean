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

import RHSignedPrimeConvolutionIntegrabilityV7

/-!
# AEGIS Ω: extend the genuine finite Chebyshev discrepancy integral

The archived Abel theorem proves that the prime-weight W is zero below x=1,
for sufficiently separated translations, and zero beyond a finite N.
Its derivative therefore vanishes outside (1,N) apart from a null endpoint.
The V6 integrand is the negative derivative times psi(x)-x.

This proof does not use RH, growth estimates, or a new explicit formula.
SOURCE CANDIDATE: exact-head Lean/kernel/axiom replay required.
-/

open Set MeasureTheory Filter Complex
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHSignedPrimeIntervalExtensionV8

open AEGIS.WeilPrimeAbelReductionV1
open AEGIS.WeilPrimeDiscrepancyV1
open AEGIS.WeilPrimeDiscrepancyEstimateV1
open AEGIS.WeilWindowExhaustionV1
open AEGIS.WeilThreeBlockTranslatedPacketsV22
open AEGIS.RHPrimePowerKernelConnectorV1
open AEGIS.RHPrimeOnlyGrowthBridgeV1
open AEGIS.RHSignedPrimeActualKernelTailV5
open AEGIS.RHSignedPrimeChebyshevFiniteBridgeV6
open AEGIS.RHSignedPrimeConvolutionIntegrabilityV7

/-- The flat lower tail of the actual prime weight forces its derivative to vanish. -/
private theorem primeWeight_deriv_zero_below_one_v8
    (g : WeilCompactSmoothGV1) (L d x : ℝ)
    (hw : LogSupportIn g (-L) L) (hd : 2 * L < d)
    (hx : 0 < x) (hx1 : x < 1) :
    deriv (PrimeWeightV1 g d) x = 0 := by
  have hevent :
      PrimeWeightV1 g d =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [eventually_gt_nhds hx, eventually_lt_nhds hx1] with y hypos hy1
    exact primeWeight_zero_below_one_v1 g L d y hw hd hypos hy1.le
  simpa only [deriv_const] using Filter.EventuallyEq.deriv_eq hevent

/-- The exact finite upper cutoff similarly makes the derivative vanish in the upper tail. -/
private theorem primeWeight_deriv_zero_above_cutoff_v8
    (g : WeilCompactSmoothGV1) (d x : ℝ) (N : ℕ)
    (hUpper : ∀ y : ℝ, (N : ℝ) ≤ y → PrimeWeightV1 g d y = 0)
    (hx : (N : ℝ) < x) :
    deriv (PrimeWeightV1 g d) x = 0 := by
  have hevent :
      PrimeWeightV1 g d =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact hUpper y hy.le
  simpa only [deriv_const] using Filter.EventuallyEq.deriv_eq hevent

/-- Every sufficiently late finite Abel integral agrees with the complete
positive-axis Chebyshev integral by support, not by a growth hypothesis. -/
theorem eventually_finite_chebyshev_integral_extends_v8 :
    EventuallyChebyshevFiniteIntegralExtendsV6 := by
  obtain ⟨L, _hL, hw⟩ :=
    logLift_has_finite_window_v1 detectingPacket
  have hw' : LogSupportIn detectingPacket (-L) L := by
    simpa [LogWindowContainsV1, LogSupportIn] using hw
  refine ⟨2 * L + 1, ?_⟩
  intro d hd N _hN hUpper
  have hdL : 2 * L < d := by linarith
  let F : ℝ → ℂ := fun x =>
    primeDiscrepancyKernelV1 detectingPacket (d - Real.log x) *
      (((Real.exp (-Real.log x / 2) *
          (Chebyshev.psi x - x) : ℝ) : ℂ) / (x : ℂ))
  change (∫ x in Ioc (1 : ℝ) (N : ℝ), F x) =
    (∫ x in Ioi (0 : ℝ), F x)
  symm
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
    measurableSet_Ioi.nullMeasurableSet
    (fun x hx => lt_trans zero_lt_one hx.1)
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hxne hx
  rcases hx with ⟨hxpos, hxoutside⟩
  have hxpos' : 0 < x := hxpos
  have hder : deriv (PrimeWeightV1 detectingPacket d) x = 0 := by
    rcases lt_trichotomy x 1 with hxsmall | hxeq | hxlarge
    · exact primeWeight_deriv_zero_below_one_v8 detectingPacket
        L d x hw' hdL hxpos' hxsmall
    · exact (hxne hxeq).elim
    · have hxN : (N : ℝ) < x := by
        by_contra hn
        exact hxoutside ⟨hxlarge, le_of_not_gt hn⟩
      exact primeWeight_deriv_zero_above_cutoff_v8
        detectingPacket d x N hUpper hxN
  have heq :
      -(deriv (PrimeWeightV1 detectingPacket d) x *
          PrimeDiscrepancyV1 x) = F x :=
    neg_abel_integrand_eq_chebyshev_integrand
      detectingPacket d x hxpos'
  simpa only [hder, zero_mul, neg_zero] using heq.symm

/-- Once the source-exact V6/V7 proofs replay, this is the dictionary without
extra hypotheses. The independent prime-only growth question is not used here. -/
theorem eventual_signed_prime_equals_combined_v8 :
    EventuallySignedPrimeEqualsCombinedOrbitV5 :=
  eventual_signed_dictionary_of_interval_extension_v7
    eventually_finite_chebyshev_integral_extends_v8

end AEGIS.RHSignedPrimeIntervalExtensionV8

#print axioms AEGIS.RHSignedPrimeIntervalExtensionV8.eventually_finite_chebyshev_integral_extends_v8
#print axioms AEGIS.RHSignedPrimeIntervalExtensionV8.eventual_signed_prime_equals_combined_v8
