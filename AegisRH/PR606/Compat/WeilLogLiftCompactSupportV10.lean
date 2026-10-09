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

import WeilLogCoordinateIsometryV21
import Mathlib.Tactic

/-!
AEGIS Ω — compact support of the logarithmic lift V10.

For every repository packet g, the logarithmic lift

  h(t) = exp(t/2) g(exp t)

has compact support.  Its support is contained in the logarithmic image of
the compact positive support of g.

This is the compactness input for the additive-correlation Mellin
factorization.

AUTHORITY_EFFECT = NONE.
-/

open Set Complex MeasureTheory
open scoped Topology

set_option autoImplicit false
noncomputable section

namespace AEGIS.WeilLogLiftCompactSupportV10

open AEGIS.WeilLogCoordinateIsometryV21

def logLiftEnvelopeV10 (g : WeilCompactSmoothGV1) : Set ℝ :=
  Real.log '' tsupport g.1

theorem logLiftEnvelope_compact_v10 (g : WeilCompactSmoothGV1) :
    IsCompact (logLiftEnvelopeV10 g) := by
  unfold logLiftEnvelopeV10
  apply g.2.2.1.image_of_continuousOn
  intro x hx
  exact
    (Real.continuousAt_log
      (ne_of_gt (g.2.2.2 hx))).continuousWithinAt

theorem logLift_tsupport_subset_v10 (g : WeilCompactSmoothGV1) :
    tsupport (logLift g.1) ⊆ logLiftEnvelopeV10 g := by
  apply closure_minimal ?_ (logLiftEnvelope_compact_v10 g).isClosed
  intro t ht
  change logLift g.1 t ≠ 0 at ht
  have hg : g.1 (Real.exp t) ≠ 0 := by
    intro hzero
    apply ht
    simp [logLift, hzero]
  have hmem : Real.exp t ∈ tsupport g.1 :=
    subset_tsupport _ hg
  refine ⟨Real.exp t, hmem, ?_⟩
  exact Real.log_exp t

theorem logLift_hasCompactSupport_v10 (g : WeilCompactSmoothGV1) :
    HasCompactSupport (logLift g.1) :=
  (logLiftEnvelope_compact_v10 g).of_isClosed_subset
    (isClosed_tsupport _) (logLift_tsupport_subset_v10 g)

theorem logLift_continuous_v10 (g : WeilCompactSmoothGV1) :
    Continuous (logLift g.1) := by
  unfold logLift
  exact
    (Complex.ofRealCLM.continuous.comp
      (Real.continuous_exp.comp
        (continuous_id.div_const 2))).mul
      (g.2.1.continuous.comp Real.continuous_exp)

theorem logLift_integrable_v10 (g : WeilCompactSmoothGV1) :
    Integrable (logLift g.1) :=
  (logLift_continuous_v10 g).integrable_of_hasCompactSupport
    (logLift_hasCompactSupport_v10 g)

end AEGIS.WeilLogLiftCompactSupportV10

#print axioms AEGIS.WeilLogLiftCompactSupportV10.logLift_tsupport_subset_v10
#print axioms AEGIS.WeilLogLiftCompactSupportV10.logLift_hasCompactSupport_v10
