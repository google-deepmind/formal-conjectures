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
import AEGISOverlay.RHKreinFourierTaylorBoundV1

/-!
# Bind the genuine correction to the finite-interval Taylor kernel

This module is the missing analytic glue between the exact order-19 correction
and the generic finite-cell checker.  It proves that the actual correction has
all moments required through order eight, identifies its real angular Fourier
transform with `correctionSymbol`, and supplies the exact eighth-derivative
norm bound consumed by the Taylor remainder layer.

No finite-grid arithmetic and no RH conclusion is asserted here.
-/

open Complex MeasureTheory FourierTransform

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinCorrectionTaylorBridgeV1

open AEGIS.RHKreinExplicitCorrectionV1
open AEGIS.RHKreinFourierTaylorBoundV1

/-- The genuine compactly supported correction has all polynomial moments
required by the eighth-order Fourier Taylor argument. -/
theorem correction_moments_up_to_eight :
    HasMomentsUpToEight correction :=
  hasMomentsUpToEight_of_continuous_compact
    correction correction_continuous correction_hasCompactSupport

/-- The actual angular Fourier correction is C^8. -/
theorem correction_angular_contDiff_eight :
    ContDiff ℝ 8 (angularFourier correction) := by
  unfold angularFourier
  exact (fourier_contDiff_eight correction correction_moments_up_to_eight).comp
    (contDiff_const.mul contDiff_id)

/-- The analytic expression used by the rational certificate is exactly the
real part of the genuine angular Fourier transform. -/
theorem correctionSymbol_eq_re_angularFourier (t : ℝ) :
    correctionSymbol t = (angularFourier correction t).re := by
  unfold angularFourier
  rw [angularScale_mul]
  exact (correction_fourier_re t).symm

/-- Exact eighth-derivative norm bound for the genuine angular correction.
The right-hand side is a time-domain L1 moment and contains no interval
arithmetic premise. -/
theorem correction_angular_eighth_derivative_norm_le (t : ℝ) :
    ‖iteratedDeriv 8 (angularFourier correction) t‖ ≤
      |angularScale| ^ 8 *
        ∫ x : ℝ,
          ‖((-2 * Real.pi * Complex.I * (x : ℂ)) ^ 8) • correction x‖ := by
  exact angular_eighth_derivative_norm_le
    correction correction_moments_up_to_eight t

end AEGIS.RHKreinCorrectionTaylorBridgeV1

#print axioms AEGIS.RHKreinCorrectionTaylorBridgeV1.correction_moments_up_to_eight
#print axioms AEGIS.RHKreinCorrectionTaylorBridgeV1.correction_angular_contDiff_eight
#print axioms AEGIS.RHKreinCorrectionTaylorBridgeV1.correctionSymbol_eq_re_angularFourier
#print axioms AEGIS.RHKreinCorrectionTaylorBridgeV1.correction_angular_eighth_derivative_norm_le
