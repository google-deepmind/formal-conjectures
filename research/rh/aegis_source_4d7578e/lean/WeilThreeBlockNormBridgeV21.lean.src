import WeilMixedAlgebraV2
import WeilDisjointEnergyV2

/-!
AEGIS Ω — three-block actual L2 norm bridge V2.1

LOCAL CANDIDATE / FORMAL_MATH_EVIDENCE_ONLY / NOT_YET_KERNEL_REPLAYED.

This module closes only the finite norm/correspondence step:
* compact-smooth Weil packets have integrable squared norm;
* for three pointwise-disjoint packets, the rational certificate's
  `weightedEnergy` is exactly the ordinary L2 energy of the ACTUAL
  `WeilMixedAlgebraV2.combo`;
* therefore the already proved `actual_three_block_bound` can be stated
  directly against that actual combo energy.

It does NOT prove any of the six analytic diagonal/off-diagonal estimates.
It does NOT prove moment conditions, full Weil negativity, the full Weil
criterion, or RH.
-/

open Set Function MeasureTheory Complex
open scoped ContDiff ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilThreeBlockNormBridgeV21

open AEGIS.WeilMixedAlgebraV2
open AEGIS.WeilThreeBlockComplexV2
open AEGIS.WeilDisjointEnergyV2

/-- A compact-smooth packet has an integrable squared norm on the real line. -/
theorem packet_energy_integrable (g : WeilCompactSmoothGV1) :
    Integrable (fun t : ℝ => ‖g.1 t‖ ^ 2) volume := by
  have hc : Continuous (fun t : ℝ => ‖g.1 t‖ ^ 2) := by
    exact g.2.1.continuous.norm.pow 2
  have hk : HasCompactSupport (fun t : ℝ => ‖g.1 t‖ ^ 2) := by
    apply HasCompactSupport.intro g.2.2.1
    intro t ht
    simp [image_eq_zero_of_notMem_tsupport ht]
  exact hc.integrable_of_hasCompactSupport hk

/--
For pointwise-disjoint packets, the exact finite certificate energy is the
ordinary L2 energy of the actual packet combination used by the repository
mixed Weil form.
-/
theorem combo_energy_identity
    (z0 z1 z2 : ℂ)
    (g0 g1 g2 : WeilCompactSmoothGV1)
    (h01 : ∀ t : ℝ, g0.1 t = 0 ∨ g1.1 t = 0)
    (h02 : ∀ t : ℝ, g0.1 t = 0 ∨ g2.1 t = 0)
    (h12 : ∀ t : ℝ, g1.1 t = 0 ∨ g2.1 t = 0) :
    weightedEnergy z0 z1 z2 (l2 g0.1) (l2 g1.1) (l2 g2.1) =
      energy (combo z0 z1 z2 g0 g1 g2).1 := by
  have h :=
    quotient_free_norm_identity
      z0 z1 z2 g0.1 g1.1 g2.1
      (packet_energy_integrable g0)
      (packet_energy_integrable g1)
      (packet_energy_integrable g2)
      h01 h02 h12
  simpa [combo, addPacket, scalePacket] using h

/--
The current six analytic estimates imply the actual repository Weil RHS bound
with no abstract `r_i`: each scale is the actual L2 norm of its packet.
-/
theorem actual_three_block_l2_bound
    (z0 z1 z2 : ℂ)
    (g0 g1 g2 : WeilCompactSmoothGV1)
    (h01disj : ∀ t : ℝ, g0.1 t = 0 ∨ g1.1 t = 0)
    (h02disj : ∀ t : ℝ, g0.1 t = 0 ∨ g2.1 t = 0)
    (h12disj : ∀ t : ℝ, g1.1 t = 0 ∨ g2.1 t = 0)
    (h0 :
      (103 / 100 : ℝ) * (l2 g0.1) ^ 2 ≤ -(B g0 g0).re)
    (h1 :
      (103 / 100 : ℝ) * (l2 g1.1) ^ 2 ≤ -(B g1 g1).re)
    (h2 :
      (103 / 100 : ℝ) * (l2 g2.1) ^ 2 ≤ -(B g2 g2).re)
    (h01 :
      ‖B g0 g1‖ ≤ (51 / 100 : ℝ) * l2 g0.1 * l2 g1.1)
    (h02 :
      ‖B g0 g2‖ ≤ (9 / 25 : ℝ) * l2 g0.1 * l2 g2.1)
    (h12 :
      ‖B g1 g2‖ ≤ (51 / 100 : ℝ) * l2 g1.1 * l2 g2.1) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2))).re ≤
      -(1 / 10 : ℝ) * energy (combo z0 z1 z2 g0 g1 g2).1 := by
  calc
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2))).re
        ≤ -(1 / 10 : ℝ) *
            weightedEnergy z0 z1 z2 (l2 g0.1) (l2 g1.1) (l2 g2.1) :=
      actual_three_block_bound
        z0 z1 z2 g0 g1 g2
        (l2 g0.1) (l2 g1.1) (l2 g2.1)
        h0 h1 h2 h01 h02 h12
    _ = -(1 / 10 : ℝ) * energy (combo z0 z1 z2 g0 g1 g2).1 := by
      rw [combo_energy_identity z0 z1 z2 g0 g1 g2 h01disj h02disj h12disj]

/--
Strict negativity follows only after an explicit positive-energy premise.
This remains a finite three-packet statement, not global Weil negativity.
-/
theorem actual_three_block_strict_negative_of_energy_pos
    (z0 z1 z2 : ℂ)
    (g0 g1 g2 : WeilCompactSmoothGV1)
    (h01disj : ∀ t : ℝ, g0.1 t = 0 ∨ g1.1 t = 0)
    (h02disj : ∀ t : ℝ, g0.1 t = 0 ∨ g2.1 t = 0)
    (h12disj : ∀ t : ℝ, g1.1 t = 0 ∨ g2.1 t = 0)
    (h0 :
      (103 / 100 : ℝ) * (l2 g0.1) ^ 2 ≤ -(B g0 g0).re)
    (h1 :
      (103 / 100 : ℝ) * (l2 g1.1) ^ 2 ≤ -(B g1 g1).re)
    (h2 :
      (103 / 100 : ℝ) * (l2 g2.1) ^ 2 ≤ -(B g2 g2).re)
    (h01 :
      ‖B g0 g1‖ ≤ (51 / 100 : ℝ) * l2 g0.1 * l2 g1.1)
    (h02 :
      ‖B g0 g2‖ ≤ (9 / 25 : ℝ) * l2 g0.1 * l2 g2.1)
    (h12 :
      ‖B g1 g2‖ ≤ (51 / 100 : ℝ) * l2 g1.1 * l2 g2.1)
    (hE : 0 < energy (combo z0 z1 z2 g0 g1 g2).1) :
    (WeilExplicitRightSideV1
      (WeilAutocorrelationV1 (combo z0 z1 z2 g0 g1 g2))).re < 0 := by
  have hbound :=
    actual_three_block_l2_bound
      z0 z1 z2 g0 g1 g2
      h01disj h02disj h12disj
      h0 h1 h2 h01 h02 h12
  nlinarith

end AEGIS.WeilThreeBlockNormBridgeV21
