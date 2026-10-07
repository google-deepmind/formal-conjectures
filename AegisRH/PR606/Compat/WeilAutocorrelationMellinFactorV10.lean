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
open scoped BigOperators Topology ComplexConjugate

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
  have hleft : logLift g.1 (p.1 + p.2) ≠ 0 := by
    intro hz
    apply hp
    simp [logCorrelationJointV10, hz]
  have hright : logLift g.1 p.2 ≠ 0 := by
    intro hz
    apply hp
    simp [logCorrelationJointV10, hz]
  have hleftS :
      p.1 + p.2 ∈ tsupport (logLift g.1) :=
    subset_tsupport _ hleft
  have hrightS :
      p.2 ∈ tsupport (logLift g.1) :=
    subset_tsupport _ hright
  refine ⟨(p.1 + p.2, p.2), ⟨hleftS, hrightS⟩, ?_⟩
  apply Prod.ext <;> simp <;> ring

theorem logCorrelationJoint_hasCompactSupport_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    HasCompactSupport (logCorrelationJointV10 g z) := by
  refine HasCompactSupport.intro
    (logCorrelationJointEnvelope_compact_v10 g) ?_
  intro p hp
  by_contra hne
  exact hp (logCorrelationJoint_support_subset_v10 g z hne)

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
  have hprod :
      Integrable (logCorrelationJointV10 g z)
        (volume.prod volume) := by
    exact
      (logCorrelationJoint_continuous_v10 g z).integrable_of_hasCompactSupport
        (logCorrelationJoint_hasCompactSupport_v10 g z)
  exact integral_integral_swap
    (f := fun v u => logCorrelationJointV10 g z (v, u))
    (by simpa [Function.uncurry_def] using hprod)

/-- Translation of the inner v-integral. -/
theorem logLaplace_shift_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) (u : ℝ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logLift g.1 (v + u)) =
      Complex.exp (-z * (u : ℂ)) * logLaplaceV10 g z := by
  let F : ℝ → ℂ := fun w =>
    Complex.exp (z * (w : ℂ)) * logLift g.1 w
  calc
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logLift g.1 (v + u))
      =
    ∫ v : ℝ,
      Complex.exp (-z * (u : ℂ)) * F (v + u) := by
        apply integral_congr_ae
        filter_upwards [] with v
        dsimp [F]
        rw [← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
    _ =
      Complex.exp (-z * (u : ℂ)) *
        (∫ v : ℝ, F (v + u)) := by
          rw [integral_const_mul]
    _ =
      Complex.exp (-z * (u : ℂ)) *
        (∫ v : ℝ, F v) := by
          rw [integral_add_right_eq_self F u]
    _ =
      Complex.exp (-z * (u : ℂ)) *
        logLaplaceV10 g z := by
          rfl

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
  filter_upwards [] with u
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_neg, map_mul, Complex.conj_ofReal]

/-- Bilateral transform of additive correlation factors exactly. -/
theorem logCorrelation_transform_factor_v10
    (g : WeilCompactSmoothGV1) (z : ℂ) :
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCorrelationV10 g v) =
      logLaplaceV10 g z *
        conj (logLaplaceV10 g (-conj z)) := by
  have hprod :
      Integrable (logCorrelationJointV10 g z)
        (volume.prod volume) := by
    exact
      (logCorrelationJoint_continuous_v10 g z).integrable_of_hasCompactSupport
        (logCorrelationJoint_hasCompactSupport_v10 g z)
  calc
    (∫ v : ℝ,
      Complex.exp (z * (v : ℂ)) *
        logCorrelationV10 g v)
      =
    ∫ v : ℝ,
      ∫ u : ℝ,
        logCorrelationJointV10 g z (v, u) := by
          apply integral_congr_ae
          filter_upwards [] with v
          unfold logCorrelationJointV10 logCorrelationV10
          rw [← integral_const_mul]
          congr 1
          funext u
          simp only [Prod.fst, Prod.snd]
          ring
    _ =
    ∫ u : ℝ,
      ∫ v : ℝ,
        logCorrelationJointV10 g z (v, u) := by
          exact integral_integral_swap
            (f := fun v u => logCorrelationJointV10 g z (v, u))
            (by simpa [Function.uncurry_def] using hprod)
    _ =
    ∫ u : ℝ,
      (Complex.exp (-z * (u : ℂ)) *
        logLaplaceV10 g z) *
        conj (logLift g.1 u) := by
          apply integral_congr_ae
          filter_upwards [] with u
          unfold logCorrelationJointV10
          simp only [Prod.fst, Prod.snd]
          rw [integral_mul_const]
          rw [logLaplace_shift_v10 g z u]
    _ =
      logLaplaceV10 g z *
        (∫ u : ℝ,
          Complex.exp (-z * (u : ℂ)) *
            conj (logLift g.1 u)) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with u
              ring
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
  unfold logLaplaceV10 WeilLogMellinIntegrandV9 logLift
  apply integral_congr_ae
  filter_upwards [] with u
  have hexp :
      Complex.exp (s * (u : ℂ)) =
        Complex.exp ((s - (1 / 2 : ℂ)) * (u : ℂ)) *
          (Real.exp (u / 2) : ℂ) := by
    rw [show
      s * (u : ℂ) =
        (s - (1 / 2 : ℂ)) * (u : ℂ) +
          (((u / 2 : ℝ) : ℂ)) by
            push_cast
            ring,
      Complex.exp_add,
      ← Complex.ofReal_exp]
  rw [hexp]
  ring

/-- THE autocorrelation Mellin factorization. -/
theorem mellin_autocorrelation_factor_v10
    (g : WeilCompactSmoothGV1) (s : ℂ) :
    mellin (WeilAutocorrelationV1 g) s =
      mellin g.1 s *
        conj (mellin g.1 (1 - conj s)) := by
  let A : WeilCompactSmoothGV1 :=
    WeilAutocorrelationCompactSmoothV1 g
  have hlog := mellin_eq_log_integral_v9 A s
  have hcoord :
      (∫ v : ℝ, WeilLogMellinIntegrandV9 A s v) =
      ∫ v : ℝ,
        Complex.exp ((s - (1 / 2 : ℂ)) * (v : ℂ)) *
          logCorrelationV10 g v := by
    apply integral_congr_ae
    filter_upwards [] with v
    unfold WeilLogMellinIntegrandV9
    rw [show A.1 (Real.exp v) =
      WeilAutocorrelationV1 g (Real.exp v) by rfl]
    rw [autocorrelation_exp_eq_logCorrelation_v10]
    have hexp :
        Complex.exp (s * (v : ℂ)) *
            ((Real.exp (-v / 2) : ℝ) : ℂ) =
          Complex.exp ((s - (1 / 2 : ℂ)) * (v : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← mul_assoc, hexp]
  rw [show mellin (WeilAutocorrelationV1 g) s =
      mellin A.1 s from rfl, hlog, hcoord,
    logCorrelation_transform_factor_v10]
  rw [logLaplace_shift_eq_mellin_v10 g s]
  have hreflect :
      -(conj (s - (1 / 2 : ℂ))) =
        (1 - conj s) - (1 / 2 : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [hreflect]
  rw [logLaplace_shift_eq_mellin_v10 g (1 - conj s)]

end AEGIS.WeilAutocorrelationMellinFactorV10

#print axioms AEGIS.WeilAutocorrelationMellinFactorV10.logCorrelation_transform_factor_v10
#print axioms AEGIS.WeilAutocorrelationMellinFactorV10.mellin_autocorrelation_factor_v10
