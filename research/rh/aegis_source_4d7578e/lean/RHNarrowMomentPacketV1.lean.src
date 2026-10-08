import WeilCriterionCompactSmoothV1
import WeilMomentKillerConstructionV1
import WeilLogTransportCanonicalV1
import WeilThreeBlockTranslatedPacketsV22
import Mathlib.Tactic

/-!
AEGIS Ω — narrow canonical moment-killed packet v1.

This is the #510 moment-killer/log-transport construction instantiated at a
narrower seed.  The seed has log-radius 1/80, so the killed profile remains
inside [-1/64,1/64].  Its multiplicative packet therefore satisfies the later
V2.2/V3.1 WidthOneThirtyTwoAt predicate exactly.

The construction uses the canonical repository definitions
WeilCompactSmoothGV1 and WeilMomentConditionsV1; it does not restate them.

No Weil sign or RH conclusion is asserted by this module.
-/

open Set MeasureTheory Filter
open scoped ContDiff Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHNarrowMomentPacketV1

open AEGIS.WeilMomentKillerConstructionV1
open AEGIS.WeilLogTransportCanonicalV1
open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilThreeBlockTranslatedPacketsV22

/-- Narrow smooth seed in the log coordinate. -/
def narrowBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 160
  rOut := 1 / 80
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def psiNarrow : ℝ → ℝ := fun u => narrowBump u

def phiNarrow : ℝ → ℝ := momentKiller psiNarrow

theorem psiNarrow_contDiff : ContDiff ℝ ∞ psiNarrow :=
  narrowBump.contDiff

theorem psiNarrow_tsupport :
    tsupport psiNarrow = closedBall (0 : ℝ) (1 / 80) := by
  show tsupport (narrowBump : ℝ → ℝ) = _
  rw [narrowBump.tsupport_eq]
  norm_num [narrowBump]

theorem psiNarrow_hasCompactSupport : HasCompactSupport psiNarrow := by
  rw [HasCompactSupport, psiNarrow_tsupport]
  exact isCompact_closedBall _ _

theorem psiNarrow_at_zero : psiNarrow 0 = 1 :=
  narrowBump.one_of_mem_closedBall (by simp [Metric.mem_closedBall, narrowBump])

/-- The moment killer does not enlarge support, so the output lies strictly
inside the later +/-1/64 log packet window. -/
theorem phiNarrow_tsupport_Icc :
    tsupport phiNarrow ⊆ Icc (-(1 / 64) : ℝ) (1 / 64) := by
  refine (tsupport_momentKiller_subset psiNarrow).trans ?_
  rw [psiNarrow_tsupport, Real.closedBall_eq_Icc]
  exact Icc_subset_Icc (by norm_num) (by norm_num)

theorem phiNarrow_vanishes_below :
    ∀ u ≤ -(1 / 64 : ℝ), phiNarrow u = 0 := by
  intro u hu
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have hs := phiNarrow_tsupport_Icc hmem
  linarith [hs.1]

theorem phiNarrow_vanishes_above :
    ∀ u, (1 / 64 : ℝ) ≤ u → phiNarrow u = 0 := by
  intro u hu
  refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
  have hs := phiNarrow_tsupport_Icc hmem
  linarith [hs.2]

theorem phiNarrow_contDiff : ContDiff ℝ ∞ phiNarrow :=
  momentKiller_contDiff psiNarrow_contDiff

theorem phiNarrow_continuous : Continuous phiNarrow :=
  phiNarrow_contDiff.continuous

theorem phiNarrow_moments :
    (∫ u : ℝ, phiNarrow u) = 0 ∧
    (∫ u : ℝ, phiNarrow u * Real.exp u) = 0 :=
  ⟨integral_momentKiller psiNarrow_contDiff psiNarrow_hasCompactSupport,
    integral_momentKiller_mul_exp psiNarrow_contDiff psiNarrow_hasCompactSupport⟩

theorem phiNarrow_ne_zero : phiNarrow ≠ 0 := by
  intro h
  change momentKiller psiNarrow = 0 at h
  have hz :=
    eq_zero_of_momentKiller_eq_zero
      psiNarrow_contDiff psiNarrow_hasCompactSupport h 0
  rw [psiNarrow_at_zero] at hz
  norm_num at hz

def narrowRealPacket : ℝ → ℝ :=
  mulPacket phiNarrow

def narrowPacketFn : ℝ → ℂ :=
  fun x => ((narrowRealPacket x : ℝ) : ℂ)

theorem narrowPacketFn_contDiff : ContDiff ℝ ∞ narrowPacketFn :=
  Complex.ofRealCLM.contDiff.comp
    (mulPacket_contDiff phiNarrow_contDiff phiNarrow_vanishes_below)

theorem narrowPacketFn_support :
    Function.support narrowPacketFn = Function.support narrowRealPacket := by
  ext x
  simp [narrowPacketFn, narrowRealPacket, Function.mem_support, Complex.ofReal_eq_zero]

theorem narrowPacketFn_hasCompactSupport : HasCompactSupport narrowPacketFn := by
  rw [HasCompactSupport, tsupport, narrowPacketFn_support, ← tsupport]
  exact mulPacket_hasCompactSupport phiNarrow_vanishes_below phiNarrow_vanishes_above

theorem narrowPacketFn_tsupport_positive :
    tsupport narrowPacketFn ⊆ Ioi (0 : ℝ) := by
  rw [tsupport, narrowPacketFn_support, ← tsupport]
  refine (tsupport_mulPacket_subset
    phiNarrow_vanishes_below phiNarrow_vanishes_above).trans ?_
  intro x hx
  exact lt_of_lt_of_le (Real.exp_pos _) hx.1

/-- Canonical repository packet. -/
def gNarrow : WeilCompactSmoothGV1 :=
  ⟨narrowPacketFn, narrowPacketFn_contDiff,
    narrowPacketFn_hasCompactSupport, narrowPacketFn_tsupport_positive⟩

/-- The canonical two moment conditions are inherited from the same generic
moment-killer identities after exact log transport. -/
theorem gNarrow_moments :
    WeilMomentConditionsV1 gNarrow := by
  constructor
  · have hreal :
        ∫ x in Ioi (0 : ℝ), x⁻¹ * narrowRealPacket x = 0 := by
      rw [integral_mulPacket_inv
        phiNarrow_continuous phiNarrow_vanishes_below phiNarrow_vanishes_above]
      exact phiNarrow_moments.1
    have hcast :
        ∫ x in Ioi (0 : ℝ), gNarrow.1 x / (x : ℂ) =
          ((∫ x in Ioi (0 : ℝ), x⁻¹ * narrowRealPacket x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      show ((narrowRealPacket x : ℝ) : ℂ) / (x : ℂ) = _
      rw [Complex.ofReal_mul, Complex.ofReal_inv]
      field_simp
    rw [hcast, hreal, Complex.ofReal_zero]
  · have hreal :
        ∫ x in Ioi (0 : ℝ), narrowRealPacket x = 0 := by
      rw [integral_mulPacket
        phiNarrow_continuous phiNarrow_vanishes_below phiNarrow_vanishes_above]
      exact phiNarrow_moments.2
    have hcast :
        ∫ x in Ioi (0 : ℝ), gNarrow.1 x =
          ((∫ x in Ioi (0 : ℝ), narrowRealPacket x : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      rfl
    rw [hcast, hreal, Complex.ofReal_zero]

theorem gNarrow_ne_zero : gNarrow.1 ≠ 0 := by
  intro h
  refine phiNarrow_ne_zero (funext fun u => ?_)
  simp only [Pi.zero_apply]
  have hx : (0 : ℝ) < Real.exp u := Real.exp_pos u
  have hc := congrFun h (Real.exp u)
  simp only [Pi.zero_apply] at hc
  have hc2 : ((narrowRealPacket (Real.exp u) : ℝ) : ℂ) = 0 := hc
  unfold narrowRealPacket at hc2
  rw [mulPacket_of_pos hx, Real.log_exp] at hc2
  exact_mod_cast hc2

theorem logLift_gNarrow_apply (t : ℝ) :
    logLift gNarrow.1 t =
      (Real.exp (t / 2) : ℂ) * (phiNarrow t : ℂ) := by
  unfold logLift gNarrow narrowPacketFn narrowRealPacket
  rw [mulPacket_of_pos (Real.exp_pos t), Real.log_exp]
  rfl

/-- The actual later log-lift support predicate, not merely x-space support. -/
theorem gNarrow_logLift_support :
    tsupport (logLift gNarrow.1) ⊆
      Icc (-(1 / 64) : ℝ) (1 / 64) := by
  apply closure_minimal
  · intro t ht
    by_contra hout
    have hphi : phiNarrow t = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      exact hout (phiNarrow_tsupport_Icc hmem)
    apply ht
    rw [logLift_gNarrow_apply, hphi]
    simp
  · exact isClosed_Icc

/-- Exact compatibility with the V2.2/V3.1 retained packet class. -/
theorem gNarrow_width :
    WidthOneThirtyTwoAt gNarrow 0 := by
  change tsupport (logLift gNarrow.1) ⊆
    Icc (0 - (1 / 64 : ℝ)) (0 + (1 / 64 : ℝ))
  simpa using gNarrow_logLift_support

end AEGIS.RHNarrowMomentPacketV1

#print axioms AEGIS.RHNarrowMomentPacketV1.gNarrow_moments
#print axioms AEGIS.RHNarrowMomentPacketV1.gNarrow_ne_zero
#print axioms AEGIS.RHNarrowMomentPacketV1.gNarrow_logLift_support
#print axioms AEGIS.RHNarrowMomentPacketV1.gNarrow_width
