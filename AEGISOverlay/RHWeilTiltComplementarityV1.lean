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


import AEGISOverlay.RHCompactMellinEntireV1
import WeilMomentAnnihilatorV1
import RestrictedWeilCriterionResidueWitnessV11

/-!
# Complementary generators in the actual Weil packet carrier

Real exponential tilting in logarithmic coordinates preserves compact smooth
positive support and shifts the Mellin transform. A generic tilt removes all
common complex Mellin zeros of a nonzero packet and its companion. The existing
two-moment finite-dilation filter then produces actual moment-zero packets
with no common Mellin zero in the open critical strip.

The filter has additional zeros on the boundary lines. No full-plane
complementarity, approximation density, or Weil sign is claimed for the
filtered pair.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped ContDiff

namespace AEGIS.RHWeilTiltComplementarityV1

/-- A real exponential tilt in the logarithmic coordinate. -/
def tiltFun (g : WeilCompactSmoothGV1) (a : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (a * Real.log x) : ℂ) * g.1 x

/-- The only possible singularity of the logarithmic weight is outside support. -/
theorem tiltFun_contDiff (g : WeilCompactSmoothGV1) (a : ℝ) :
    ContDiff ℝ ∞ (tiltFun g a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hnot : (0 : ℝ) ∉ tsupport g.1 := by
      intro hz
      exact (lt_irrefl (0 : ℝ)) (g.2.2.2 hz)
    have hg0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    have hEq : tiltFun g a =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℂ) := by
      filter_upwards [hg0] with y hy
      simp [tiltFun, hy]
    exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const hEq
  · have hw : ContDiffAt ℝ ∞ (fun y : ℝ => Real.exp (a * Real.log y)) x :=
      Real.contDiff_exp.contDiffAt.comp x
        (contDiffAt_const.mul (Real.contDiffAt_log.mpr hx))
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hw).mul g.2.1.contDiffAt

/-- Tilting preserves topological support containment. -/
theorem tiltFun_tsupport_subset (g : WeilCompactSmoothGV1) (a : ℝ) :
    tsupport (tiltFun g a) ⊆ tsupport g.1 :=
  tsupport_mul_subset_right

/-- The tilted function is in the exact repository packet carrier. -/
def tiltPacket (g : WeilCompactSmoothGV1) (a : ℝ) : WeilCompactSmoothGV1 :=
  ⟨tiltFun g a, tiltFun_contDiff g a, g.2.2.1.mul_left,
    (tiltFun_tsupport_subset g a).trans g.2.2.2⟩

/-- The globally smooth definition agrees with complex-power weighting. -/
theorem tiltFun_eq_cpow (g : WeilCompactSmoothGV1) (a : ℝ) :
    tiltFun g a = fun x : ℝ => (x : ℂ) ^ (a : ℂ) • g.1 x := by
  funext x
  by_cases hx : 0 < x
  · have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    have hw : (Real.exp (a * Real.log x) : ℂ) = (x : ℂ) ^ (a : ℂ) := by
      rw [Complex.cpow_def_of_ne_zero hxc, ← Complex.ofReal_log hx.le,
        Complex.ofReal_exp, Complex.ofReal_mul]
      congr 1
      ring
    unfold tiltFun
    rw [hw, smul_eq_mul]
  · have hnot : x ∉ tsupport g.1 := fun h => hx (g.2.2.2 h)
    have hg0 := image_eq_zero_of_notMem_tsupport hnot
    simp [tiltFun, hg0]

/-- Exact Mellin transport for actual smooth packets. -/
theorem mellin_tiltPacket (g : WeilCompactSmoothGV1) (a : ℝ) (s : ℂ) :
    mellin (tiltPacket g a).1 s = mellin g.1 (s + (a : ℂ)) := by
  change mellin (tiltFun g a) s = _
  rw [tiltFun_eq_cpow, mellin_cpow_smul]

/-- Every actual packet with a nonzero Mellin value has an actual companion
whose Mellin transform shares no complex zero. -/
theorem exists_packet_companion (g : WeilCompactSmoothGV1)
    (z₀ : ℂ) (hz₀ : mellin g.1 z₀ ≠ 0) :
    ∃ q : WeilCompactSmoothGV1, ∀ z : ℂ,
      ¬ (mellin g.1 z = 0 ∧ mellin q.1 z = 0) := by
  obtain ⟨a, ha⟩ :=
    AEGIS.RHGenericSpectralShiftV1.exists_real_shift_no_common_zero_of_entire
      (mellin g.1) (AEGIS.RHCompactMellinEntireV1.packet_mellin_entire g) z₀ hz₀
  refine ⟨tiltPacket g a, ?_⟩
  intro z
  rw [mellin_tiltPacket]
  exact ha z

/-- The existing moment filter preserves complementarity throughout the open
critical strip, where its multiplier is known to be nonzero. -/
theorem exists_moment_zero_complementary_pair (g : WeilCompactSmoothGV1)
    (z₀ : ℂ) (hz₀ : mellin g.1 z₀ ≠ 0) :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∀ z : ℂ, 0 < z.re → z.re < 1 →
        ¬ (mellin p.1 z = 0 ∧ mellin q.1 z = 0) := by
  obtain ⟨q, hq⟩ := exists_packet_companion g z₀ hz₀
  refine ⟨WeilMomentAnnihilatorV1 g, WeilMomentAnnihilatorV1 q,
    weil_moment_annihilator_moments_v1 g, weil_moment_annihilator_moments_v1 q, ?_⟩
  intro z hz0 hz1
  rintro ⟨hp, hqz⟩
  rw [weil_moment_annihilator_mellin_v1] at hp hqz
  have hm := weil_moment_annihilator_multiplier_ne_zero_v1 hz0 hz1
  exact hq z ⟨(mul_eq_zero.mp hp).resolve_left hm,
    (mul_eq_zero.mp hqz).resolve_left hm⟩

/-- An unconditional pair of actual compact smooth moment-zero packets has no
common Mellin zero anywhere in the open critical strip. -/
theorem unconditional_moment_zero_complementary_pair :
    ∃ p q : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 p ∧ WeilMomentConditionsV1 q ∧
      ∀ z : ℂ, 0 < z.re → z.re < 1 →
        ¬ (mellin p.1 z = 0 ∧ mellin q.1 z = 0) := by
  let g := AEGIS.RestrictedWeilCriterionResidueWitnessV11.TargetPacketV11 (2 : ℂ)
  have hg : mellin g.1 (2 : ℂ) ≠ 0 :=
    AEGIS.RestrictedWeilCriterionResidueWitnessV11.targetPacket_mellin_target_ne_zero_v11
      2 (by norm_num) (by norm_num)
  exact exists_moment_zero_complementary_pair g 2 hg

#print axioms AEGIS.RHWeilTiltComplementarityV1.tiltFun_contDiff
#print axioms AEGIS.RHWeilTiltComplementarityV1.mellin_tiltPacket
#print axioms AEGIS.RHWeilTiltComplementarityV1.exists_packet_companion
#print axioms AEGIS.RHWeilTiltComplementarityV1.unconditional_moment_zero_complementary_pair

end AEGIS.RHWeilTiltComplementarityV1

