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

import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Uniform bound for a translated bounded factor through an L1 kernel

If a complex-valued factor P is uniformly bounded by B and k is integrable,
then every translated convolution slice

  d ↦ ∫ k(u) P(d-u) du

is bounded by B times the L1 norm of k.

This is the abstract analytic bridge needed after the normalized higher
prime-power discrepancy has been shown bounded.  It does not supply the
prime-only bound and does not prove RH.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open MeasureTheory

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHBoundedConvolutionV1

theorem norm_integral_mul_shift_le_v1
    (μ : Measure ℝ) (k P : ℝ → ℂ) (B d : ℝ)
    (hk : Integrable k μ)
    (hP : ∀ x : ℝ, ‖P x‖ ≤ B) :
    ‖∫ u : ℝ, k u * P (d - u) ∂μ‖ ≤
      B * ∫ u : ℝ, ‖k u‖ ∂μ := by
  have hmajor : Integrable (fun u : ℝ => B * ‖k u‖) μ :=
    hk.norm.const_mul B
  refine (norm_integral_le_of_norm_le hmajor ?_).trans_eq ?_
  · exact Filter.Eventually.of_forall (fun u => by
      rw [norm_mul]
      calc
        ‖k u‖ * ‖P (d - u)‖ ≤ ‖k u‖ * B :=
          mul_le_mul_of_nonneg_left (hP (d - u)) (norm_nonneg _)
        _ = B * ‖k u‖ := by ring)
  · rw [integral_const_mul]

#print axioms AEGIS.RHBoundedConvolutionV1.norm_integral_mul_shift_le_v1

end AEGIS.RHBoundedConvolutionV1
