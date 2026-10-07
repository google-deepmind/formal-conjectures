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

import RHKreinExplicitCorrectionV1
import Mathlib.Tactic

/-!
# Exact M8 payload for the order-19 finite Krein certificate

The numerical checker uses a degree-seven Taylor jet for the correction and
the uniform eighth-derivative budget

  M8 =
    sum_i 2*w*|a_i|*(u_i+w)^8
    + sum_j |b_j|*(2/h)^j*(L+19*h)^8.

This module recomputes that quantity entirely in rational arithmetic from
the exact coefficients already compiled into RHKreinExplicitCorrectionV1
and proves that it equals the rational value serialized in
krein_order19_v1/certificate.json.

This theorem validates the exact arithmetic payload only. The analytic
statement |C^(8)(t)| <= M8 is a separate proof obligation.

AUTHORITY_EFFECT = NONE.
RH is not asserted here.
-/

open scoped BigOperators

set_option autoImplicit false

namespace AEGIS.RHKreinM8CertificateV1

open AEGIS.RHKreinExplicitCorrectionV1

def hatCenterQ (j : Fin 199) : ℚ :=
  ((j.val : ℚ) + 41) / 50

def certificateM8Q : ℚ :=
  (∑ j : Fin 199,
      2 * (1 / 50 : ℚ) * |hatCoefficient j| *
        (hatCenterQ j + 1 / 50) ^ 8) +
    ∑ j : Fin 5,
      |splineCoefficient j| *
        (2 : ℚ) ^ j.val / (1 / 1000 : ℚ) ^ j.val *
        (819 / 1000 : ℚ) ^ 8

def serializedM8Q : ℚ :=
  15958085437561175275197089938898547979087185237 /
    5000000000000000000000000000000000

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem certificateM8_eq_serialized_v1 :
    certificateM8Q = serializedM8Q := by
  norm_num [certificateM8Q, serializedM8Q, hatCenterQ,
    hatCoefficient, splineCoefficient, Fin.sum_univ_succ]

theorem serializedM8Q_pos_v1 : 0 < serializedM8Q := by
  norm_num [serializedM8Q]

end AEGIS.RHKreinM8CertificateV1

#print axioms AEGIS.RHKreinM8CertificateV1.certificateM8_eq_serialized_v1
#print axioms AEGIS.RHKreinM8CertificateV1.serializedM8Q_pos_v1
