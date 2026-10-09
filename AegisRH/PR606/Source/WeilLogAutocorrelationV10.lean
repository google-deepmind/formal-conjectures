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

import WeilLogLiftCompactSupportV10
import WeilCriterionCompactSmoothV1
import Mathlib.Tactic

/-!
AEGIS Ω — multiplicative/autocorrelation log-coordinate identity V10.

For h = logLift g define the additive correlation

  C_g(v) = ∫ h(v+u) conj(h(u)) du.

Then the repository's multiplicative autocorrelation satisfies exactly

  Autocorrelation(g)(exp v) = exp(-v/2) C_g(v).

This is a direct x=exp(u) substitution; no asymptotic or sign hypothesis is
used.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilLogAutocorrelationV10

open AEGIS.WeilLogCoordinateIsometryV21

def logCorrelationV10 (g : WeilCompactSmoothGV1) (v : ℝ) : ℂ :=
  ∫ u : ℝ,
    logLift g.1 (v + u) * conj (logLift g.1 u)

private theorem logCorrelation_integrand_identity_v10
    (g : WeilCompactSmoothGV1) (v u : ℝ) :
    ((Real.exp (-v / 2) : ℝ) : ℂ) *
      (logLift g.1 (v + u) * conj (logLift g.1 u)) =
    ((Real.exp u : ℝ) : ℂ) *
      (g.1 (Real.exp v * Real.exp u) *
        conj (g.1 (Real.exp u))) := by
  unfold logLift
  have hev : Real.exp (v + u) = Real.exp v * Real.exp u := by
    rw [Real.exp_add]
  rw [hev]
  simp only [map_mul, conj_ofReal]
  have hscalar :
      Real.exp (-v / 2) *
        (Real.exp ((v + u) / 2) * Real.exp (u / 2)) =
      Real.exp u := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  push_cast [hscalar]
  ring

/-- Exact conversion of the repository autocorrelation to additive
log-correlation. -/
theorem autocorrelation_exp_eq_logCorrelation_v10
    (g : WeilCompactSmoothGV1) (v : ℝ) :
    WeilAutocorrelationV1 g (Real.exp v) =
      ((Real.exp (-v / 2) : ℝ) : ℂ) *
        logCorrelationV10 g v := by
  have hsub :=
    integral_comp_exp
      (fun y : ℝ =>
        g.1 (Real.exp v * y) * conj (g.1 y))
  change
    WeilAutocorrelationV1 g (Real.exp v) =
      ((Real.exp (-v / 2) : ℝ) : ℂ) *
        (∫ u : ℝ,
          logLift g.1 (v + u) * conj (logLift g.1 u))
  unfold WeilAutocorrelationV1
  rw [← hsub]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    simpa [smul_eq_mul] using
      logCorrelation_integrand_identity_v10 g v u)

end AEGIS.WeilLogAutocorrelationV10

#print axioms AEGIS.WeilLogAutocorrelationV10.autocorrelation_exp_eq_logCorrelation_v10
