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
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Coefficients of `exp (L)` for a power series `L`

For a power series `L` with zero constant coefficient, the coefficients of the composition
$\exp(L)$ can be computed recursively: differentiating $A = \exp(L)$ gives $A' = A L'$, so
$$(m + 1) a_{m+1} = \sum_{i=0}^{m} a_i (m - i + 1) \ell_{m - i + 1}.$$
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A] {L : A⟦X⟧}

/-- The constant coefficient of `exp (L)` is `1` when `L` has zero constant coefficient. -/
theorem coeff_zero_subst_exp (hL : constantCoeff L = 0) : coeff 0 ((exp A).subst L) = 1 := by
  rw [coeff_subst' (.of_constantCoeff_zero' hL), finsum_eq_single _ 0]
  · simp
  · intro d hd
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, hL, zero_pow hd, smul_zero]

/-- The coefficients of `exp (L)` satisfy the recurrence obtained by differentiating
`exp (L)`. -/
theorem coeff_succ_subst_exp_mul (hL : constantCoeff L = 0) (m : ℕ) :
    coeff (m + 1) ((exp A).subst L) * (m + 1) = ∑ i ∈ Finset.range (m + 1),
      coeff i ((exp A).subst L) * (coeff (m - i + 1) L * (m - i + 1 : ℕ)) := by
  have h := congrArg (coeff m) (derivative_subst (f := exp A) (.of_constantCoeff_zero' hL))
  rw [derivative_exp, coeff_derivative, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa [coeff_derivative] using h

end PowerSeries
