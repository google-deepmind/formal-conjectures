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

import Mathlib.NumberTheory.Chebyshev

/-!
# Prime-power correction is bounded after critical normalization

Mathlib proves the unconditional Costa-Pereira estimate

  ψ(x) - θ(x) = O(√x).

Under the logarithmic coordinate x = exp(y), the normalization used by the
AEGIS prime-discrepancy kernel multiplies this difference by exp(-y/2).
The square-root growth therefore cancels exactly, leaving a uniform bound.

This isolates higher prime powers as a bounded perturbation.  It does not
bound the remaining prime-only discrepancy θ(x)-x and does not prove RH.

AUTHORITY_EFFECT = NONE.
RH_PROVEN_UNCONDITIONALLY = false.
-/

open Real

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHPrimePowerBoundedV1

/-- Exact square-root identity in logarithmic coordinates. -/
theorem sqrt_exp_eq_exp_half_v1 (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hexp :
      Real.exp y = (Real.exp (y / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The higher-prime-power discrepancy is uniformly bounded after the
critical exp(-y/2) normalization. -/
theorem normalized_prime_power_correction_bounded_v1 :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ,
      |Real.exp (-y / 2) *
        (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y))| ≤ B := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y
  have hdiff0 :
      0 ≤ Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  have hnorm0 : 0 ≤ Real.exp (-y / 2) := (Real.exp_pos _).le
  have hbound := hC (Real.exp y)
  rw [sqrt_exp_eq_exp_half_v1] at hbound
  rw [abs_of_nonneg (mul_nonneg hnorm0 hdiff0)]
  calc
    Real.exp (-y / 2) *
        (Chebyshev.psi (Real.exp y) - Chebyshev.theta (Real.exp y))
        ≤ Real.exp (-y / 2) * (C * Real.exp (y / 2)) :=
      mul_le_mul_of_nonneg_left hbound hnorm0
    _ = C := by
      calc
        Real.exp (-y / 2) * (C * Real.exp (y / 2))
            = C * (Real.exp (-y / 2) * Real.exp (y / 2)) := by ring
        _ = C * Real.exp ((-y / 2) + (y / 2)) := by rw [Real.exp_add]
        _ = C := by
          have hzero : (-y / 2) + (y / 2) = 0 := by ring
          rw [hzero, Real.exp_zero, mul_one]
    _ ≤ max C 0 := le_max_left _ _

#print axioms AEGIS.RHPrimePowerBoundedV1.sqrt_exp_eq_exp_half_v1
#print axioms AEGIS.RHPrimePowerBoundedV1.normalized_prime_power_correction_bounded_v1

end AEGIS.RHPrimePowerBoundedV1
