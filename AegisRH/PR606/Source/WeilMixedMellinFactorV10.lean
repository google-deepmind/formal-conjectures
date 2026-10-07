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
open scoped BigOperators Topology ComplexConjugate

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
  have ha : logLift a.1 (p.1 + p.2) ≠ 0 := by
    intro hz
    apply hp
    simp [logCrossJointV10, hz]
  have hb : logLift b.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    simp [logCrossJointV10, hz]
  refine
    ⟨(p.1 + p.2, p.2),
      ⟨subset_tsupport _ ha, subset_tsupport _ hb⟩, ?_⟩
  apply Prod.ext <;> simp <;> ring

theorem logCrossJoint_hasCompactSupport_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    HasCompactSupport (logCrossJointV10 a b z) := by
  apply HasCompactSupport.intro
    (logCrossJointEnvelope_compact_v10 a b)
  intro p hp
  by_contra hne
  apply hp
  exact logCrossJoint_support_subset_v10 a b z hne

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
  have hprod :
      Integrable (logCrossJointV10 a b z)
        (volume.prod volume) := by
    exact
      (logCrossJoint_continuous_v10 a b z).integrable_of_hasCompactSupport
        (logCrossJoint_hasCompactSupport_v10 a b z)
  exact integral_integral_swap
    (f := fun v u => logCrossJointV10 a b z (v, u))
    (by simpa [Function.uncurry_def] using hprod)

theorem logCross_transform_factor_v10
    (a b : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCrossV28 a b v) =
      logLaplaceV10 a z *
        conj (logLaplaceV10 b (-conj z)) := by
  have hprod :
      Integrable (logCrossJointV10 a b z)
        (volume.prod volume) := by
    exact
      (logCrossJoint_continuous_v10 a b z).integrable_of_hasCompactSupport
        (logCrossJoint_hasCompactSupport_v10 a b z)
  calc
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCrossV28 a b v)
      =
    ∫ v : ℝ,
      ∫ u : ℝ,
        logCrossJointV10 a b z (v, u) := by
          apply integral_congr_ae
          filter_upwards [] with v
          unfold logCrossJointV10 logCrossV28
          rw [← integral_const_mul]
          congr 1
          funext u
          simp only [Prod.fst, Prod.snd]
          ring
    _ =
    ∫ u : ℝ,
      ∫ v : ℝ,
        logCrossJointV10 a b z (v, u) := by
          exact integral_integral_swap
            (f := fun v u => logCrossJointV10 a b z (v, u))
            (by simpa [Function.uncurry_def] using hprod)
    _ =
    ∫ u : ℝ,
      (Complex.exp (-z * (u : ℂ)) *
        logLaplaceV10 a z) *
        conj (logLift b.1 u) := by
          apply integral_congr_ae
          filter_upwards [] with u
          unfold logCrossJointV10
          simp only [Prod.fst, Prod.snd]
          rw [integral_mul_const]
          rw [logLaplace_shift_v10 a z u]
    _ =
      logLaplaceV10 a z *
        (∫ u : ℝ,
          Complex.exp (-z * (u : ℂ)) *
            conj (logLift b.1 u)) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with u
              ring
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
            mixed a b (Real.exp v) =
          Complex.exp ((s - 1 / 2) * (v : ℂ)) *
            logCrossV28 a b v
      have hcross := logCross_eq_mixed_v28 a b v
      rw [hcross, Complex.ofReal_exp]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2 <;> push_cast <;> ring)
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
