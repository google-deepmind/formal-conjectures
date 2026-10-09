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

import RestrictedWeilCriterionTargetWitnessV11
import RestrictedWeilCriterionKernelBridgeV10
import WeilAutocorrelationMellinV11
import WeilZeroTwoPointV11
import WeilPairedZeroEvaluationV9
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
AEGIS Ω — transport the targeted log witness into the actual Weil test domain.

For every nontrivial zeta zero rho this module constructs a compact-smooth
multiplicative packet with both AEGIS moment conditions and nonzero Mellin
value at rho.  It then combines the rho-targeted packet with the
(1-conj rho)-targeted packet using one coefficient lambda chosen from
{0,1,I}.  The combined packet has nonzero Mellin values at both spectral
points, so its multiplicative autocorrelation Mellin value at rho is nonzero.

This is the residue witness required by the restricted-Weil pole argument.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Topology ContDiff ComplexConjugate

set_option autoImplicit false
noncomputable section

namespace AEGIS.RestrictedWeilCriterionResidueWitnessV11

open AEGIS.RestrictedWeilCriterionTargetWitnessV11
open AEGIS.RestrictedWeilCriterionKernelBridgeV10
open AEGIS.WeilAutocorrelationMellinV11
open AEGIS.WeilZeroTwoPointV11
open AEGIS.WeilMomentKillerConstructionV1

private theorem targetPsi_tsupport_subset_psi0_v11 (rho : ℂ) :
    tsupport (TargetPsiV11 rho) ⊆ tsupport psi0 := by
  have hbase :
      tsupport (fun u : ℝ => (psi0 u : ℂ)) = tsupport psi0 := by
    rw [tsupport, tsupport]
    congr 1
    ext u
    simp [Function.mem_support]
  intro u hu
  have hu' :
      u ∈ tsupport (fun u : ℝ => (psi0 u : ℂ)) := by
    unfold TargetPsiV11 at hu
    exact tsupport_mul_subset_left hu
  rwa [hbase] at hu'

private theorem targetPhi_vanishes_below_v11
    (rho : ℂ) {u : ℝ} (hu : u ≤ -(1 / 32 : ℝ)) :
    TargetPhiV11 rho u = 0 := by
  have hnot0 : u ∉ tsupport psi0 := by
    rw [psi0_tsupport, Real.closedBall_eq_Icc]
    intro h
    linarith [h.1]
  have hnotPsi : u ∉ tsupport (TargetPsiV11 rho) := by
    intro h
    exact hnot0 (targetPsi_tsupport_subset_psi0_v11 rho h)
  have h1 : deriv (TargetPsiV11 rho) u = 0 :=
    deriv_of_notMem_tsupport hnotPsi
  have hnotD : u ∉ tsupport (deriv (TargetPsiV11 rho)) := by
    intro h
    exact hnotPsi (tsupport_deriv_subset h)
  have h2 : deriv (deriv (TargetPsiV11 rho)) u = 0 :=
    deriv_of_notMem_tsupport hnotD
  simp [TargetPhiV11, h1, h2]

private theorem targetPhi_vanishes_above_v11
    (rho : ℂ) {u : ℝ} (hu : (1 / 32 : ℝ) ≤ u) :
    TargetPhiV11 rho u = 0 := by
  have hnot0 : u ∉ tsupport psi0 := by
    rw [psi0_tsupport, Real.closedBall_eq_Icc]
    intro h
    linarith [h.2]
  have hnotPsi : u ∉ tsupport (TargetPsiV11 rho) := by
    intro h
    exact hnot0 (targetPsi_tsupport_subset_psi0_v11 rho h)
  have h1 : deriv (TargetPsiV11 rho) u = 0 :=
    deriv_of_notMem_tsupport hnotPsi
  have hnotD : u ∉ tsupport (deriv (TargetPsiV11 rho)) := by
    intro h
    exact hnotPsi (tsupport_deriv_subset h)
  have h2 : deriv (deriv (TargetPsiV11 rho)) u = 0 :=
    deriv_of_notMem_tsupport hnotD
  simp [TargetPhiV11, h1, h2]

/-- Guarded multiplicative transport of the targeted log witness. -/
def TargetPacketFunV11 (rho : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then TargetPhiV11 rho (Real.log x) else 0

private theorem targetPacketFun_of_pos_v11
    (rho : ℂ) {x : ℝ} (hx : 0 < x) :
    TargetPacketFunV11 rho x =
      TargetPhiV11 rho (Real.log x) := by
  simp [TargetPacketFunV11, hx]

private theorem targetPacketFun_eq_zero_below_v11
    (rho : ℂ) {x : ℝ}
    (hx : x ≤ Real.exp (-(1 / 32 : ℝ))) :
    TargetPacketFunV11 rho x = 0 := by
  rcases le_or_gt x 0 with hnonpos | hpos
  · simp [TargetPacketFunV11, not_lt.mpr hnonpos]
  · rw [targetPacketFun_of_pos_v11 rho hpos]
    apply targetPhi_vanishes_below_v11 rho
    have hlog :=
      (Real.log_le_log_iff hpos
        (Real.exp_pos (-(1 / 32 : ℝ)))).2 hx
    simpa using hlog

private theorem targetPacketFun_eq_zero_above_v11
    (rho : ℂ) {x : ℝ}
    (hx : Real.exp (1 / 32 : ℝ) ≤ x) :
    TargetPacketFunV11 rho x = 0 := by
  have hpos : 0 < x :=
    lt_of_lt_of_le (Real.exp_pos (1 / 32 : ℝ)) hx
  rw [targetPacketFun_of_pos_v11 rho hpos]
  apply targetPhi_vanishes_above_v11 rho
  have hlog :=
    (Real.log_le_log_iff
      (Real.exp_pos (1 / 32 : ℝ)) hpos).2 hx
  simpa using hlog

theorem targetPacketFun_contDiff_v11 (rho : ℂ) :
    ContDiff ℝ ∞ (TargetPacketFunV11 rho) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge 0 x with hx | hx
  · have hEq :
        TargetPacketFunV11 rho =ᶠ[𝓝 x]
          fun y => TargetPhiV11 rho (Real.log y) :=
      eventuallyEq_of_mem (Ioi_mem_nhds hx)
        (fun y hy => targetPacketFun_of_pos_v11 rho hy)
    exact ContDiffAt.congr_of_eventuallyEq
      ((targetPhi_contDiff_v11 rho).contDiffAt.comp x
        (Real.contDiffAt_log.2 (ne_of_gt hx))) hEq
  · have hmem :
        Iio (Real.exp (-(1 / 32 : ℝ))) ∈ 𝓝 x :=
      Iio_mem_nhds
        (lt_of_le_of_lt hx (Real.exp_pos (-(1 / 32 : ℝ))))
    have hEq :
        TargetPacketFunV11 rho =ᶠ[𝓝 x] fun _ => (0 : ℂ) :=
      eventuallyEq_of_mem hmem
        (fun y hy =>
          targetPacketFun_eq_zero_below_v11 rho (le_of_lt hy))
    exact
      ContDiffAt.congr_of_eventuallyEq contDiffAt_const hEq

theorem targetPacketFun_tsupport_subset_v11 (rho : ℂ) :
    tsupport (TargetPacketFunV11 rho) ⊆
      Icc (Real.exp (-(1 / 32 : ℝ)))
        (Real.exp (1 / 32 : ℝ)) := by
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hnot
  apply hx
  rcases not_and_or.mp (fun h => hnot ⟨h.1, h.2⟩) with h | h
  · exact targetPacketFun_eq_zero_below_v11 rho (le_of_not_ge h)
  · exact targetPacketFun_eq_zero_above_v11 rho (le_of_not_ge h)

theorem targetPacketFun_hasCompactSupport_v11 (rho : ℂ) :
    HasCompactSupport (TargetPacketFunV11 rho) := by
  exact
    (isCompact_Icc : IsCompact
      (Icc (Real.exp (-(1 / 32 : ℝ)))
        (Real.exp (1 / 32 : ℝ)))).of_isClosed_subset
      (isClosed_tsupport _)
      (targetPacketFun_tsupport_subset_v11 rho)

theorem targetPacketFun_positive_support_v11 (rho : ℂ) :
    tsupport (TargetPacketFunV11 rho) ⊆ Ioi 0 := by
  intro x hx
  have hwin := targetPacketFun_tsupport_subset_v11 rho hx
  exact lt_of_lt_of_le
    (Real.exp_pos (-(1 / 32 : ℝ))) hwin.1

/-- Actual compact-smooth multiplicative packet. -/
def TargetPacketV11 (rho : ℂ) : WeilCompactSmoothGV1 :=
  ⟨TargetPacketFunV11 rho,
    targetPacketFun_contDiff_v11 rho,
    targetPacketFun_hasCompactSupport_v11 rho,
    targetPacketFun_positive_support_v11 rho⟩

/-- Exact logarithmic Mellin representation of the transported witness. -/
theorem targetPacket_mellin_log_v11 (rho s : ℂ) :
    mellin (TargetPacketV11 rho).1 s =
      ∫ u : ℝ,
        Complex.exp (s * (u : ℂ)) *
          TargetPhiV11 rho u := by
  rw [AEGIS.WeilPairedZeroEvaluationV9.mellin_eq_log_integral_v9]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    unfold AEGIS.WeilPairedZeroEvaluationV9.WeilLogMellinIntegrandV9
    change
      Complex.exp (s * (u : ℂ)) *
          TargetPacketFunV11 rho (Real.exp u) =
        _
    rw [targetPacketFun_of_pos_v11 rho (Real.exp_pos u),
      Real.log_exp])

/-- Both repository moment conditions are discharged exactly. -/
theorem targetPacket_moments_v11 (rho : ℂ) :
    WeilMomentConditionsV1 (TargetPacketV11 rho) := by
  apply
    (moment_conditions_iff_mellin_endpoints_zero_v10
      (TargetPacketV11 rho)).mpr
  constructor
  · rw [targetPacket_mellin_log_v11]
    simpa using targetPhi_integral_zero_v11 rho
  · rw [targetPacket_mellin_log_v11]
    have h := targetPhi_exp_integral_zero_v11 rho
    simpa [Complex.ofReal_exp, mul_comm] using h

/-- At its target spectral parameter, the transported packet has the exact
nonzero Mellin value constructed in log coordinates. -/
theorem targetPacket_mellin_target_ne_zero_v11
    (rho : ℂ) (hr0 : rho ≠ 0) (hr1 : rho ≠ 1) :
    mellin (TargetPacketV11 rho).1 rho ≠ 0 := by
  rw [targetPacket_mellin_log_v11]
  simpa [smul_eq_mul, mul_comm] using
    targetPhi_weighted_integral_ne_zero_of_ne_zero_one_v11
      rho hr0 hr1

/-- Two affine constraints over ℂ can be avoided using only the three choices
0, 1 and I, provided the two diagonal coefficients are nonzero. -/
private theorem exists_lambda_affine_pair_nonzero_v11
    (A B C D : ℂ) (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ lam : ℂ,
      A + lam * B ≠ 0 ∧
      C + lam * D ≠ 0 := by
  by_cases hC : C ≠ 0
  · exact ⟨0, by simpa using hA, by simpa using hC⟩
  · have hC0 : C = 0 := not_ne_iff.mp hC
    by_cases h1 : A + B ≠ 0
    · refine ⟨1, ?_, ?_⟩
      · simpa using h1
      · simpa [hC0] using hD
    · have hAB : A + B = 0 := not_ne_iff.mp h1
      have hB : B = -A := by
        linear_combination hAB
      refine ⟨I, ?_, ?_⟩
      · rw [hB]
        have h1mI : (1 - I : ℂ) ≠ 0 := by
          intro h
          have him := congrArg Complex.im h
          simp at him
        convert mul_ne_zero hA h1mI using 1 <;> ring
      · rw [hC0, zero_add]
        exact mul_ne_zero I_ne_zero hD

/-- For each nontrivial zero rho, build one moment-zero packet whose Mellin
transform is nonzero at both rho and the reflected point 1-conj(rho). -/
theorem exists_residue_packet_v11
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin g.1 rho.1 ≠ 0 ∧
      mellin g.1 (1 - conj rho.1) ≠ 0 := by
  let sigma : ℂ := 1 - conj rho.1
  have hstrip :=
    riemann_zeta_nontrivial_zero_critical_strip_v1
      rho.2.1 rho.2.2

  have hr0 : rho.1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.1]
  have hr1 : rho.1 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hstrip.2]

  have hsre : sigma.re = 1 - rho.1.re := by
    simp [sigma]
  have hs0 : sigma ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    simp at hre
    linarith [hstrip.2]
  have hs1 : sigma ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    simp at hre
    linarith [hstrip.1]

  let p := TargetPacketV11 rho.1
  let q := TargetPacketV11 sigma
  let A : ℂ := mellin p.1 rho.1
  let B : ℂ := mellin q.1 rho.1
  let C : ℂ := mellin p.1 sigma
  let D : ℂ := mellin q.1 sigma

  have hA : A ≠ 0 := by
    dsimp [A, p]
    exact targetPacket_mellin_target_ne_zero_v11 rho.1 hr0 hr1
  have hD : D ≠ 0 := by
    dsimp [D, q]
    exact targetPacket_mellin_target_ne_zero_v11 sigma hs0 hs1

  obtain ⟨lam, hleft, hright⟩ :=
    exists_lambda_affine_pair_nonzero_v11 A B C D hA hD

  let g : WeilCompactSmoothGV1 :=
    AEGIS.WeilMixedAlgebraV2.addPacket p
      (AEGIS.WeilMixedAlgebraV2.scalePacket lam q)

  refine ⟨g, ?_, ?_, ?_⟩
  · dsimp [g]
    exact addPacket_preserves_moments_v10
      p (AEGIS.WeilMixedAlgebraV2.scalePacket lam q)
      (targetPacket_moments_v11 rho.1)
      (scalePacket_preserves_moments_v10
        lam q (targetPacket_moments_v11 sigma))
  · dsimp [g, A, B, p, q] at hleft ⊢
    rw [AEGIS.WeilZeroTwoPointV11.mellin_addPacket_v11,
      AEGIS.WeilZeroTwoPointV11.mellin_scalePacket_v11]
    exact hleft
  · dsimp [g, C, D, p, q, sigma] at hright ⊢
    rw [AEGIS.WeilZeroTwoPointV11.mellin_addPacket_v11,
      AEGIS.WeilZeroTwoPointV11.mellin_scalePacket_v11]
    exact hright

/-- The residue packet has nonzero autocorrelation Mellin coefficient at rho. -/
theorem exists_residue_packet_autocorrelation_mellin_ne_zero_v11
    (rho : RiemannNontrivialZeroIndexV2) :
    ∃ g : WeilCompactSmoothGV1,
      WeilMomentConditionsV1 g ∧
      mellin (WeilAutocorrelationV1 g) rho.1 ≠ 0 := by
  obtain ⟨g, hm, hr, href⟩ :=
    exists_residue_packet_v11 rho
  refine ⟨g, hm, ?_⟩
  rw [AEGIS.WeilAutocorrelationMellinV11.weil_autocorrelation_mellin_factorization_v11]
  exact mul_ne_zero hr ((map_ne_zero (starRingEnd ℂ)).2 href)

end AEGIS.RestrictedWeilCriterionResidueWitnessV11

#print axioms AEGIS.RestrictedWeilCriterionResidueWitnessV11.targetPacket_moments_v11
#print axioms AEGIS.RestrictedWeilCriterionResidueWitnessV11.targetPacket_mellin_target_ne_zero_v11
#print axioms AEGIS.RestrictedWeilCriterionResidueWitnessV11.exists_residue_packet_v11
#print axioms AEGIS.RestrictedWeilCriterionResidueWitnessV11.exists_residue_packet_autocorrelation_mellin_ne_zero_v11
