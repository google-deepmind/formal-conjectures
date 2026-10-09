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

import AEGISOverlay.RHKreinSplineContinuityV1
import Mathlib.Tactic

/-!
# Moving-average derivative primitive for the Krein M8 closure

The order-19 spline is a repeated convolution with the normalized interval
box.  This module proves the ordinary derivative identity for one averaging
step.  It is the FTC input for the exact L1 estimate used by the M8 certificate.

No numerical certificate and no RH statement is asserted here.
AUTHORITY_EFFECT = NONE.
-/

open Set MeasureTheory Convolution

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinSplineL1DerivativeBoundV1

open AEGIS.RHKreinSplineSupportV1
open AEGIS.RHKreinSplineContinuityV1

/-- Exact derivative of convolution with the normalized interval box. -/
theorem deriv_convolution_normalizedBox
    (f : ℝ → ℂ) (hf : Continuous f) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    deriv (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) x =
      (h : ℂ)⁻¹ * (f (x + h / 2) - f (x - h / 2)) := by
  have hfun :
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] normalizedBox h) =
        fun y : ℝ =>
          (h : ℂ)⁻¹ *
            ((∫ u in (0 : ℝ)..(y + h / 2), f u) -
              ∫ u in (0 : ℝ)..(y - h / 2), f u) := by
    funext y
    rw [convolution_normalizedBox f hh.le y,
      intervalIntegral.integral_interval_sub_left
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have hp0 :
      HasDerivAt (fun z : ℝ => ∫ u in (0 : ℝ)..z, f u)
        (f (x + h / 2)) (x + h / 2) :=
    (hf.integral_hasStrictDerivAt 0 (x + h / 2)).hasDerivAt
  have hm0 :
      HasDerivAt (fun z : ℝ => ∫ u in (0 : ℝ)..z, f u)
        (f (x - h / 2)) (x - h / 2) :=
    (hf.integral_hasStrictDerivAt 0 (x - h / 2)).hasDerivAt
  have hp :
      HasDerivAt (fun y : ℝ => ∫ u in (0 : ℝ)..(y + h / 2), f u)
        (f (x + h / 2)) x := by
    simpa only [Function.comp_def, one_smul] using
      hp0.scomp x ((hasDerivAt_id' x).add_const (h / 2))
  have hm :
      HasDerivAt (fun y : ℝ => ∫ u in (0 : ℝ)..(y - h / 2), f u)
        (f (x - h / 2)) x := by
    simpa only [Function.comp_def, one_smul] using
      hm0.scomp x ((hasDerivAt_id' x).sub_const (h / 2))
  rw [hfun]
  exact ((hp.sub hm).const_mul ((h : ℂ)⁻¹)).deriv

end AEGIS.RHKreinSplineL1DerivativeBoundV1

#print axioms AEGIS.RHKreinSplineL1DerivativeBoundV1.deriv_convolution_normalizedBox
