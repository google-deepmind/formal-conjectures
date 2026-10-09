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

import V13Scratch

/-!
AEGIS Ω — restricted Weil criterion terminal V13.

This file promotes the already-developed V13 pole/resolvent contradiction out
of scratch naming and binds it directly to the Millennium gate's exact
restricted-criterion field.

It does NOT supply the universal zero-quadratic nonnegativity producer.
Consequently it does not by itself inhabit RHMillenniumCertificateV10.

AUTHORITY_EFFECT = NONE.
-/

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHRestrictedWeilCriterionV13

open AEGIS.RHMillenniumGateV10

/-- Exact kernelized restricted-Weil implication consumed by the gate. -/
theorem restricted_weil_criterion_v13 :
    RestrictedWeilCriterionKernelBridgeV10 :=
  AEGIS.V13Scratch.restricted_weil_criterion_kernel_bridge_v13

/-- Once a universal zero-quadratic producer is supplied, the current V13
terminal immediately yields Mathlib's exact RiemannHypothesis type. -/
theorem universal_zero_quadratic_implies_mathlib_rh_v13
    (h : UniversalZeroQuadraticNonnegativeV10) :
    RiemannHypothesis :=
  restricted_weil_criterion_v13 h

/-- The Millennium certificate now has exactly one missing field: the
unconditional universal-zero-quadratic producer. -/
def certificate_of_universal_zero_quadratic_v13
    (h : UniversalZeroQuadraticNonnegativeV10) :
    RHMillenniumCertificateV10 where
  universal_zero_quadratic := h
  restricted_criterion := restricted_weil_criterion_v13

end AEGIS.RHRestrictedWeilCriterionV13

#print axioms AEGIS.RHRestrictedWeilCriterionV13.restricted_weil_criterion_v13
#print axioms AEGIS.RHRestrictedWeilCriterionV13.universal_zero_quadratic_implies_mathlib_rh_v13
#print axioms AEGIS.RHRestrictedWeilCriterionV13.certificate_of_universal_zero_quadratic_v13
