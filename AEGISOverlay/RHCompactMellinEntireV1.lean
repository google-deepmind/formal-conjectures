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


import WeilMellinInversionV1
import AEGISOverlay.RHGenericSpectralShiftV1

/-!
# Entire Mellin transforms of the actual compact smooth Weil packets

Compact support bounds the packet away from both zero and infinity. Mathlib's
Mellin differentiability theorem then applies on an arbitrary vertical strip,
so the Mellin transform is entire. The generic real spectral shift theorem
therefore applies to every packet with a specified nonzero Mellin value.

The power-tilted function is used in the ordinary Mellin transform. Its
membership in the smooth packet carrier is not needed or asserted here.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Asymptotics

namespace AEGIS.RHCompactMellinEntireV1

/-- Compact positive support makes the actual packet's Mellin transform entire. -/
theorem packet_mellin_entire (g : WeilCompactSmoothGV1) :
    AnalyticOnNhd ℂ (mellin g.1) Set.univ := by
  have htop : g.1 =ᶠ[atTop] 0 := by
    have hc := g.2.2.1
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hc
    exact hc.filter_mono atTop_le_cocompact
  have hzero : (0 : ℝ) ∉ tsupport g.1 := by
    intro hz
    exact (lt_irrefl (0 : ℝ)) (g.2.2.2 hz)
  have hnear : g.1 =ᶠ[𝓝[>] (0 : ℝ)] 0 :=
    (notMem_tsupport_iff_eventuallyEq.mp hzero).filter_mono nhdsWithin_le_nhds
  have hlocal : LocallyIntegrableOn g.1 (Set.Ioi (0 : ℝ)) :=
    g.2.1.continuous.locallyIntegrable.locallyIntegrableOn _
  have hdiff : Differentiable ℂ (mellin g.1) := by
    intro s
    have htopO : g.1 =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1))) := by
      apply Asymptotics.IsBigO.of_bound 0
      filter_upwards [htop] with x hx
      simp [hx]
    have hnearO : g.1 =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(s.re - 1))) := by
      apply Asymptotics.IsBigO.of_bound 0
      filter_upwards [hnear] with x hx
      simp [hx]
    exact mellin_differentiableAt_of_isBigO_rpow hlocal htopO (by linarith)
      hnearO (by linarith)
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

/-- A genuine Weil packet with one nonzero Mellin value admits a complementary
real-power tilt at every complex spectral point. -/
theorem packet_exists_mellin_power_tilt_no_common_zero
    (g : WeilCompactSmoothGV1) (z₀ : ℂ) (hz₀ : mellin g.1 z₀ ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ,
      ¬ (mellin g.1 z = 0 ∧
        mellin (fun x => (x : ℂ) ^ (a : ℂ) • g.1 x) z = 0) :=
  AEGIS.RHGenericSpectralShiftV1.exists_mellin_power_tilt_no_common_zero
    g.1 (packet_mellin_entire g) z₀ hz₀

/-- The moment polynomial adds exactly its two required shared roots. -/
theorem packet_moment_polynomial_common_zeros_exact
    (g : WeilCompactSmoothGV1) (z₀ : ℂ) (hz₀ : mellin g.1 z₀ ≠ 0) :
    ∃ a : ℝ, ∀ z : ℂ,
      (z * (z - 1) * mellin g.1 z = 0 ∧
        z * (z - 1) * mellin g.1 (z + (a : ℂ)) = 0) ↔
          z = 0 ∨ z = 1 :=
  AEGIS.RHGenericSpectralShiftV1.moment_polynomial_common_zeros_exact
    (mellin g.1) (packet_mellin_entire g) z₀ hz₀

#print axioms AEGIS.RHCompactMellinEntireV1.packet_mellin_entire
#print axioms AEGIS.RHCompactMellinEntireV1.packet_exists_mellin_power_tilt_no_common_zero
#print axioms AEGIS.RHCompactMellinEntireV1.packet_moment_polynomial_common_zeros_exact

end AEGIS.RHCompactMellinEntireV1

