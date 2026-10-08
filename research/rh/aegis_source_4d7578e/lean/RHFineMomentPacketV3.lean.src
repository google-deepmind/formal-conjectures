import WeilCriterionCompactSmoothV1
import WeilMomentKillerConstructionV1
import WeilLogTransportCanonicalV1
import RHNarrowDiagonalUpgradeV2
import Mathlib.Tactic

/-!
AEGIS Omega -- a genuinely finer canonical moment-zero packet, candidate V3.
The seed radius 1/256 is strictly smaller than the target half-width 1/128.
Endpoint vanishing is proved from that strict containment, not inferred from
membership in a closed target interval. Existing gNarrow is not reclassified.
Canonical repository carrier and moment definitions are imported, not restated.
Pinned Lean replay and the transitive axiom audit remain required.
-/

open Set MeasureTheory Filter
open scoped ContDiff Topology
set_option autoImplicit false
noncomputable section

namespace AEGIS.RHFineMomentPacketV3
open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilLogTransportCanonicalV1
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.RHNarrowDiagonalUpgradeV2

/-- A new seed, not the older radius-1/80 seed. -/
def fineBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 512
  rOut := 1 / 256
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def psiFine : ℝ → ℝ := fun u => fineBump u

def phiFine : ℝ → ℝ := momentKiller psiFine

theorem psiFine_contDiff_v3 : ContDiff ℝ ∞ psiFine := fineBump.contDiff

theorem psiFine_tsupport_v3 :
    tsupport psiFine = Metric.closedBall (0 : ℝ) (1 / 256) := by
  show tsupport (fineBump : ℝ → ℝ) = _
  rw [fineBump.tsupport_eq]
  norm_num [fineBump]

theorem psiFine_hasCompactSupport_v3 : HasCompactSupport psiFine := by
  rw [HasCompactSupport, psiFine_tsupport_v3]
  exact isCompact_closedBall _ _

theorem psiFine_at_zero_v3 : psiFine 0 = 1 :=
  fineBump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, fineBump])

/-- Closed support inside a STRICTLY smaller interval than the target. -/
theorem phiFine_tsupport_strict_v3 :
    tsupport phiFine ⊆ Icc (-(1 / 256) : ℝ) (1 / 256) := by
  refine (tsupport_momentKiller_subset psiFine).trans ?_
  rw [psiFine_tsupport_v3, Real.closedBall_eq_Icc]
  exact Icc_subset_Icc (by norm_num) (by norm_num)

theorem phiFine_vanishes_below_v3 :
    ∀ u ≤ -(1 / 128 : ℝ), phiFine u = 0 := by
  intro u hu
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hs := phiFine_tsupport_strict_v3 hmem
  linarith [hs.1]

theorem phiFine_vanishes_above_v3 :
    ∀ u, (1 / 128 : ℝ) ≤ u → phiFine u = 0 := by
  intro u hu
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hs := phiFine_tsupport_strict_v3 hmem
  linarith [hs.2]

theorem phiFine_contDiff_v3 : ContDiff ℝ ∞ phiFine :=
  momentKiller_contDiff psiFine_contDiff_v3

theorem phiFine_moments_v3 :
    (∫ u : ℝ, phiFine u) = 0 ∧
    (∫ u : ℝ, phiFine u * Real.exp u) = 0 :=
  ⟨integral_momentKiller psiFine_contDiff_v3 psiFine_hasCompactSupport_v3,
   integral_momentKiller_mul_exp psiFine_contDiff_v3 psiFine_hasCompactSupport_v3⟩

theorem phiFine_ne_zero_v3 : phiFine ≠ 0 := by
  intro h
  change momentKiller psiFine = 0 at h
  have hz := eq_zero_of_momentKiller_eq_zero
    psiFine_contDiff_v3 psiFine_hasCompactSupport_v3 h 0
  rw [psiFine_at_zero_v3] at hz
  norm_num at hz

def fineRealPacket : ℝ → ℝ := mulPacket phiFine

def finePacketFn : ℝ → ℂ := fun x => (fineRealPacket x : ℂ)

theorem finePacketFn_contDiff_v3 : ContDiff ℝ ∞ finePacketFn :=
  Complex.ofRealCLM.contDiff.comp
    (mulPacket_contDiff phiFine_contDiff_v3 phiFine_vanishes_below_v3)

theorem finePacketFn_support_v3 :
    Function.support finePacketFn = Function.support fineRealPacket := by
  ext x
  simp [finePacketFn, fineRealPacket, Function.mem_support, Complex.ofReal_eq_zero]

theorem finePacketFn_hasCompactSupport_v3 : HasCompactSupport finePacketFn := by
  rw [HasCompactSupport, tsupport, finePacketFn_support_v3, ← tsupport]
  exact mulPacket_hasCompactSupport phiFine_vanishes_below_v3 phiFine_vanishes_above_v3

theorem finePacketFn_tsupport_positive_v3 : tsupport finePacketFn ⊆ Ioi (0 : ℝ) := by
  rw [tsupport, finePacketFn_support_v3, ← tsupport]
  refine (tsupport_mulPacket_subset
    phiFine_vanishes_below_v3 phiFine_vanishes_above_v3).trans ?_
  intro x hx
  exact lt_of_lt_of_le (Real.exp_pos _) hx.1

def gFine : WeilCompactSmoothGV1 :=
  ⟨finePacketFn, finePacketFn_contDiff_v3,
    finePacketFn_hasCompactSupport_v3, finePacketFn_tsupport_positive_v3⟩

theorem gFine_moments_v3 : WeilMomentConditionsV1 gFine := by
  constructor
  · have hreal : ∫ x in Ioi (0 : ℝ), x⁻¹ * fineRealPacket x = 0 := by
      unfold fineRealPacket
      rw [integral_mulPacket_inv phiFine_contDiff_v3.continuous
        phiFine_vanishes_below_v3 phiFine_vanishes_above_v3]
      exact phiFine_moments_v3.1
    have hcast : (∫ x in Ioi (0 : ℝ), gFine.1 x / (x : ℂ)) =
        ((∫ x in Ioi (0 : ℝ), x⁻¹ * fineRealPacket x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      show (fineRealPacket x : ℂ) / (x : ℂ) = ((x⁻¹ * fineRealPacket x : ℝ) : ℂ)
      push_cast
      rw [div_eq_inv_mul]
    rw [hcast, hreal, Complex.ofReal_zero]
  · have hreal : ∫ x in Ioi (0 : ℝ), fineRealPacket x = 0 := by
      unfold fineRealPacket
      rw [integral_mulPacket phiFine_contDiff_v3.continuous
        phiFine_vanishes_below_v3 phiFine_vanishes_above_v3]
      exact phiFine_moments_v3.2
    have hcast : (∫ x in Ioi (0 : ℝ), gFine.1 x) =
        ((∫ x in Ioi (0 : ℝ), fineRealPacket x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      rfl
    rw [hcast, hreal, Complex.ofReal_zero]

theorem gFine_ne_zero_v3 : gFine.1 ≠ 0 := by
  intro h
  refine phiFine_ne_zero_v3 (funext fun u => ?_)
  simp only [Pi.zero_apply]
  have hc := congrFun h (Real.exp u)
  simp only [Pi.zero_apply] at hc
  have hc2 : (fineRealPacket (Real.exp u) : ℂ) = 0 := hc
  unfold fineRealPacket at hc2
  rw [mulPacket_of_pos (Real.exp_pos u), Real.log_exp] at hc2
  exact_mod_cast hc2

theorem logLift_gFine_apply_v3 (t : ℝ) :
    logLift gFine.1 t = (Real.exp (t / 2) : ℂ) * (phiFine t : ℂ) := by
  show (Real.exp (t / 2) : ℂ) * (fineRealPacket (Real.exp t) : ℂ) = _
  unfold fineRealPacket
  rw [mulPacket_of_pos (Real.exp_pos t), Real.log_exp]

theorem gFine_width_v3 : WidthOneSixtyFourAt gFine 0 := by
  change tsupport (logLift gFine.1) ⊆ Icc (0 - 1 / 128) (0 + 1 / 128)
  apply closure_minimal
  · intro t ht
    by_contra hout
    have hphi : phiFine t = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hs := phiFine_tsupport_strict_v3 hmem
      apply hout
      constructor <;> linarith [hs.1, hs.2]
    apply ht
    rw [logLift_gFine_apply_v3, hphi]
    simp
  · exact isClosed_Icc

end AEGIS.RHFineMomentPacketV3

#print axioms AEGIS.RHFineMomentPacketV3.psiFine_contDiff_v3
#print axioms AEGIS.RHFineMomentPacketV3.psiFine_tsupport_v3
#print axioms AEGIS.RHFineMomentPacketV3.psiFine_hasCompactSupport_v3
#print axioms AEGIS.RHFineMomentPacketV3.psiFine_at_zero_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_tsupport_strict_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_vanishes_below_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_vanishes_above_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_contDiff_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_moments_v3
#print axioms AEGIS.RHFineMomentPacketV3.phiFine_ne_zero_v3
#print axioms AEGIS.RHFineMomentPacketV3.finePacketFn_contDiff_v3
#print axioms AEGIS.RHFineMomentPacketV3.finePacketFn_support_v3
#print axioms AEGIS.RHFineMomentPacketV3.finePacketFn_hasCompactSupport_v3
#print axioms AEGIS.RHFineMomentPacketV3.finePacketFn_tsupport_positive_v3
#print axioms AEGIS.RHFineMomentPacketV3.gFine_moments_v3
#print axioms AEGIS.RHFineMomentPacketV3.gFine_ne_zero_v3
#print axioms AEGIS.RHFineMomentPacketV3.logLift_gFine_apply_v3
#print axioms AEGIS.RHFineMomentPacketV3.gFine_width_v3
