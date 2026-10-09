import WeilAutocorrelationMellinFactorV10
import WeilThreeBlockCrossPrimeV28
import WeilMixedClosureV2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
AEGIS Ω — exact mixed Mellin factorization V10.

For arbitrary repository packets a,b,

  M(mixed a b)(s)
    = M a(s) * conj(M b(1-conj s)).

This is the sesquilinear extension of the autocorrelation theorem.  The proof
uses the existing exact log-coordinate mixed identity from V28 and compact-
support Fubini.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilMixedMellinFactorV10

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilLogLiftCompactSupportV10
open AEGIS.WeilAutocorrelationMellinFactorV10
open AEGIS.WeilThreeBlockCrossPrimeV28
open AEGIS.WeilMixedClosureV2
open AEGIS.WeilPairedZeroEvaluationV9

def logCrossJointV10
    (a b : WeilCompactSmoothGV1) (z : ℂ)
    (p : ℝ × ℝ) : ℂ :=
  Complex.exp (z * (p.1 : ℂ)) *
    logLift a.1 (p.1 + p.2) *
    conj (logLift b.1 p.2)

def logCrossJointEnvelopeV10
    (a b : WeilCompactSmoothGV1) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (p.1 - p.2, p.2)) ''
    (tsupport (logLift a.1) ×ˢ tsupport (logLift b.1))

theorem logCrossJointEnvelope_compact_v10
    (a b : WeilCompactSmoothGV1) :
    IsCompact (logCrossJointEnvelopeV10 a b) := by
  unfold logCrossJointEnvelopeV10
  exact
    ((logLift_hasCompactSupport_v10 a).prod
      (logLift_hasCompactSupport_v10 b)).image
      (by fun_prop)

theorem logCrossJoint_support_subset_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    Function.support (logCrossJointV10 a b z) ⊆
      logCrossJointEnvelopeV10 a b := by
  intro p hp
  have hprod :
      logLift a.1 (p.1 + p.2) *
        conj (logLift b.1 p.2) ≠ 0 := by
    intro h
    apply hp
    unfold logCrossJointV10
    rw [h, mul_zero]
  have ha : logLift a.1 (p.1 + p.2) ≠ 0 := by
    exact fun h => hprod (by simp [h])
  have hb : logLift b.1 p.2 ≠ 0 := by
    exact fun h => hprod (by simp [h])
  refine
    ⟨(p.1 + p.2, p.2),
      ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, ?_⟩
  apply Prod.ext
  · simp
  · rfl

theorem logCrossJoint_hasCompactSupport_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    HasCompactSupport (logCrossJointV10 a b z) :=
  HasCompactSupport.intro
    (logCrossJointEnvelope_compact_v10 a b)
    (logCrossJoint_support_subset_v10 a b z)

theorem logCrossJoint_continuous_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    Continuous (logCrossJointV10 a b z) := by
  unfold logCrossJointV10
  have ha := logLift_continuous_v10 a
  have hb := logLift_continuous_v10 b
  fun_prop

theorem logCrossJoint_fubini_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      ∫ u : ℝ, logCrossJointV10 a b z (v,u)) =
      ∫ u : ℝ,
        ∫ v : ℝ, logCrossJointV10 a b z (v,u) := by
  exact integral_integral_swap_of_hasCompactSupport
    (logCrossJoint_continuous_v10 a b z)
    (logCrossJoint_hasCompactSupport_v10 a b z)

theorem logCross_transform_factor_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCrossV28 a b v) =
      logLaplaceV10 a z *
        conj (logLaplaceV10 b (-conj z)) := by
  have hfub := logCrossJoint_fubini_v10 a b z
  have hleft :
      (∫ v : ℝ,
        ∫ u : ℝ, logCrossJointV10 a b z (v,u)) =
      ∫ v : ℝ,
        Complex.exp (z * (v : ℂ)) *
          logCrossV28 a b v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => by
      unfold logCrossJointV10 logCrossV28
      rw [integral_const_mul])
  rw [hleft] at hfub
  calc
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCrossV28 a b v)
      =
      ∫ u : ℝ,
        ∫ v : ℝ, logCrossJointV10 a b z (v,u) := hfub
    _ =
      ∫ u : ℝ,
        (Complex.exp (-z * (u : ℂ)) *
          logLaplaceV10 a z) *
          conj (logLift b.1 u) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u => by
            unfold logCrossJointV10
            rw [← integral_mul_const]
            have hs := logLaplace_shift_v10 a z u
            rw [hs]
            ring)
    _ =
      logLaplaceV10 a z *
        (∫ u : ℝ,
          Complex.exp (-z * (u : ℂ)) *
            conj (logLift b.1 u)) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u => by ring)
    _ =
      logLaplaceV10 a z *
        conj (logLaplaceV10 b (-conj z)) := by
          rw [reflected_logLaplace_integral_v10]

/-- Exact mixed Mellin factorization. -/
theorem mellin_mixed_factor_v10
    (a b : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (mixed a b) s =
      mellin a.1 s *
        conj (mellin b.1 (1 - conj s)) := by
  let m : WeilCompactSmoothGV1 := asPacket a b
  change mellin m.1 s = _
  rw [mellin_eq_log_integral_v9 m s]
  have hcoord :
      (∫ v : ℝ, WeilLogMellinIntegrandV9 m s v) =
      ∫ v : ℝ,
        Complex.exp ((s - 1 / 2) * (v : ℂ)) *
          logCrossV28 a b v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => by
      unfold WeilLogMellinIntegrandV9
      change
        Complex.exp (s * (v : ℂ)) *
          mixed a b (Real.exp v) = _
      have hcross := logCross_eq_mixed_v28 a b v
      rw [hcross]
      rw [← Complex.ofReal_exp, ← Complex.exp_ofReal]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring)
  rw [hcoord, logCross_transform_factor_v10]
  rw [logLaplace_shift_eq_mellin_v10 a s]
  have hreflect :
      -(conj (s - 1 / 2)) =
        (1 - conj s) - 1 / 2 := by
    apply Complex.ext <;> simp <;> ring
  rw [hreflect]
  rw [logLaplace_shift_eq_mellin_v10 b (1 - conj s)]

end AEGIS.WeilMixedMellinFactorV10

#print axioms AEGIS.WeilMixedMellinFactorV10.logCross_transform_factor_v10
#print axioms AEGIS.WeilMixedMellinFactorV10.mellin_mixed_factor_v10
