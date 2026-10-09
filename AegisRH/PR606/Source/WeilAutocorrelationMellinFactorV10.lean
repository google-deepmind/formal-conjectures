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

import WeilLogAutocorrelationV10
import WeilLogLiftCompactSupportV10
import WeilPairedZeroEvaluationV9
import WeilAutocorrelationClosureV1
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
AEGIS Ω — exact Mellin factorization of the multiplicative autocorrelation V10.

For h = logLift g and
  C(v) = ∫ h(v+u) * conj(h u) du,
the bilateral exponential transform satisfies

  ∫ exp(z v) C(v) dv
    = L_h(z) * conj(L_h(-conj z)).

The proof is ordinary Fubini on a continuous compactly-supported joint
integrand.  Translating back through the exact logarithmic Mellin
representation gives

  M(Autocorrelation g)(s)
    = M g(s) * conj(M g(1-conj s)).

This is the load-bearing zero-quadratic factorization; no RH or sign
assumption is used.

AUTHORITY_EFFECT = NONE.
-/

open Set Filter Topology Complex MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilAutocorrelationMellinFactorV10

open AEGIS.WeilLogCoordinateIsometryV21
open AEGIS.WeilLogLiftCompactSupportV10
open AEGIS.WeilLogAutocorrelationV10
open AEGIS.WeilPairedZeroEvaluationV9

/-- Bilateral exponential transform of the logarithmic lift. -/
def logLaplaceV10 (g : WeilCompactSmoothGV1) (z : ℂ) : ℂ :=
  ∫ u : ℝ,
    Complex.exp (z * (u : ℂ)) * logLift g.1 u

/-- Joint correlation-transform integrand. -/
def logCorrelationJointV10
    (g : WeilCompactSmoothGV1) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (z * (p.1 : ℂ)) *
    logLift g.1 (p.1 + p.2) *
    conj (logLift g.1 p.2)

/-- Compact envelope obtained from the two support variables
w=v+u and u. -/
def logCorrelationJointEnvelopeV10
    (g : WeilCompactSmoothGV1) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (p.1 - p.2, p.2)) ''
    (tsupport (logLift g.1) ×ˢ tsupport (logLift g.1))

theorem logCorrelationJointEnvelope_compact_v10
    (g : WeilCompactSmoothGV1) :
    IsCompact (logCorrelationJointEnvelopeV10 g) := by
  unfold logCorrelationJointEnvelopeV10
  exact
    ((logLift_hasCompactSupport_v10 g).prod
      (logLift_hasCompactSupport_v10 g)).image
      (by fun_prop)

theorem logCorrelationJoint_support_subset_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    Function.support (logCorrelationJointV10 g z) ⊆
      logCorrelationJointEnvelopeV10 g := by
  intro p hp
  have hprod :
      logLift g.1 (p.1 + p.2) *
        conj (logLift g.1 p.2) ≠ 0 := by
    intro h
    apply hp
    unfold logCorrelationJointV10
    rw [h, mul_zero]
  have hleft : logLift g.1 (p.1 + p.2) ≠ 0 := by
    exact fun h => hprod (by simp [h])
  have hright : logLift g.1 p.2 ≠ 0 := by
    exact fun h => hprod (by simp [h])
  have hleftS :
      p.1 + p.2 ∈ tsupport (logLift g.1) :=
    subset_tsupport _ hleft
  have hrightS :
      p.2 ∈ tsupport (logLift g.1) :=
    subset_tsupport _ hright
  refine ⟨(p.1 + p.2, p.2), ⟨hleftS, hrightS⟩, ?_⟩
  apply Prod.ext
  · simp
  · rfl

theorem logCorrelationJoint_hasCompactSupport_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    HasCompactSupport (logCorrelationJointV10 g z) :=
  HasCompactSupport.intro
    (logCorrelationJointEnvelope_compact_v10 g)
    (logCorrelationJoint_support_subset_v10 g z)

theorem logCorrelationJoint_continuous_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    Continuous (logCorrelationJointV10 g z) := by
  unfold logCorrelationJointV10
  have hLift := logLift_continuous_v10 g
  fun_prop

/-- Product Fubini for the correlation transform. -/
theorem logCorrelationJoint_fubini_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      ∫ u : ℝ,
        logCorrelationJointV10 g z (v, u)) =
      ∫ u : ℝ,
        ∫ v : ℝ,
          logCorrelationJointV10 g z (v, u) := by
  exact integral_integral_swap_of_hasCompactSupport
    (logCorrelationJoint_continuous_v10 g z)
    (logCorrelationJoint_hasCompactSupport_v10 g z)

/-- Translation of the inner v-integral. -/
theorem logLaplace_shift_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) (u : ℝ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logLift g.1 (v + u)) =
      Complex.exp (-z * (u : ℂ)) * logLaplaceV10 g z := by
  let F : ℝ → ℂ := fun w =>
    Complex.exp (z * ((w - u : ℝ) : ℂ)) *
      logLift g.1 w
  have hshift := integral_add_right_eq_self F u
  have hleft :
      (fun v : ℝ => F (v + u)) =
        (fun v : ℝ =>
          Complex.exp (z * (v : ℂ)) *
            logLift g.1 (v + u)) := by
    funext v
    dsimp [F]
    congr 2
    push_cast
    ring
  have hright :
      (fun w : ℝ => F w) =
        (fun w : ℝ =>
          Complex.exp (-z * (u : ℂ)) *
            (Complex.exp (z * (w : ℂ)) * logLift g.1 w)) := by
    funext w
    dsimp [F]
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hleft, hright] at hshift
  rw [integral_const_mul] at hshift
  simpa [logLaplaceV10] using hshift

/-- The reflected weighted integral is the conjugate reflected Laplace
transform. -/
theorem reflected_logLaplace_integral_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ u : ℝ,
      Complex.exp (-z * (u : ℂ)) *
        conj (logLift g.1 u)) =
      conj (logLaplaceV10 g (-conj z)) := by
  rw [logLaplaceV10, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp
    ring)

/-- Bilateral transform of additive correlation factors exactly. -/
theorem logCorrelation_transform_factor_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCorrelationV10 g v) =
      logLaplaceV10 g z *
        conj (logLaplaceV10 g (-conj z)) := by
  have hfub := logCorrelationJoint_fubini_v10 g z
  have hleft :
      (∫ v : ℝ,
        ∫ u : ℝ,
          logCorrelationJointV10 g z (v, u)) =
      ∫ v : ℝ,
        Complex.exp (z * (v : ℂ)) *
          logCorrelationV10 g v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => by
      unfold logCorrelationJointV10 logCorrelationV10
      rw [integral_const_mul])
  rw [hleft] at hfub
  calc
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCorrelationV10 g v)
      =
      ∫ u : ℝ,
        ∫ v : ℝ,
          logCorrelationJointV10 g z (v, u) := hfub
    _ =
      ∫ u : ℝ,
        (Complex.exp (-z * (u : ℂ)) *
          logLaplaceV10 g z) *
          conj (logLift g.1 u) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u => by
            unfold logCorrelationJointV10
            rw [← integral_mul_const]
            have hs := logLaplace_shift_v10 g z u
            rw [hs]
            ring)
    _ =
      logLaplaceV10 g z *
        (∫ u : ℝ,
          Complex.exp (-z * (u : ℂ)) *
            conj (logLift g.1 u)) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun u => by ring)
    _ =
      logLaplaceV10 g z *
        conj (logLaplaceV10 g (-conj z)) := by
          rw [reflected_logLaplace_integral_v10]

/-- Mellin transform is the bilateral transform of the logarithmic lift at
the shifted exponent s-1/2. -/
theorem logLaplace_shift_eq_mellin_v10
    (g : WeilCompactSmoothGV1) (s : ℂ) :
    logLaplaceV10 g (s - 1 / 2) = mellin g.1 s := by
  rw [mellin_eq_log_integral_v9]
  unfold logLaplaceV10
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    unfold WeilLogMellinIntegrandV9 logLift
    rw [← Complex.ofReal_exp]
    rw [← Complex.exp_ofReal]
    have h :
        Complex.exp ((s - 1 / 2) * (u : ℂ)) *
          (Complex.exp ((u / 2 : ℝ) : ℂ) * g.1 (Real.exp u)) =
        Complex.exp (s * (u : ℂ)) * g.1 (Real.exp u) := by
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    exact h)

/-- THE autocorrelation Mellin factorization. -/
theorem mellin_autocorrelation_factor_v10
    (g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilAutocorrelationV1 g) s =
      mellin g.1 s *
        conj (mellin g.1 (1 - conj s)) := by
  let A : WeilCompactSmoothGV1 :=
    WeilAutocorrelationCompactSmoothV1 g
  rw [show WeilAutocorrelationV1 g = A.1 by rfl]
  rw [mellin_eq_log_integral_v9 A s]
  have hcoord :
      (∫ v : ℝ, WeilLogMellinIntegrandV9 A s v) =
      ∫ v : ℝ,
        Complex.exp ((s - 1 / 2) * (v : ℂ)) *
          logCorrelationV10 g v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun v => by
      unfold WeilLogMellinIntegrandV9
      change
        Complex.exp (s * (v : ℂ)) *
          WeilAutocorrelationV1 g (Real.exp v) = _
      rw [autocorrelation_exp_eq_logCorrelation_v10]
      rw [← Complex.ofReal_exp]
      rw [← Complex.exp_ofReal]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring)
  rw [hcoord, logCorrelation_transform_factor_v10]
  rw [logLaplace_shift_eq_mellin_v10 g s]
  have hreflect :
      -(conj (s - 1 / 2)) =
        (1 - conj s) - 1 / 2 := by
    apply Complex.ext <;> simp <;> ring
  rw [hreflect]
  rw [logLaplace_shift_eq_mellin_v10 g (1 - conj s)]

end AEGIS.WeilAutocorrelationMellinFactorV10

#print axioms AEGIS.WeilAutocorrelationMellinFactorV10.logCorrelation_transform_factor_v10
#print axioms AEGIS.WeilAutocorrelationMellinFactorV10.mellin_autocorrelation_factor_v10
