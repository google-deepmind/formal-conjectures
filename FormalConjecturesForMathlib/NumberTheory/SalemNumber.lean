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

public import FormalConjecturesForMathlib.NumberTheory.PisotNumber

@[expose] public section
/-!
# Salem numbers

A real number `τ > 1` integral over `ℤ` is called a *Salem number* when all remaining complex
Galois conjugates of `τ` over `ℚ` satisfy `‖z‖ ≤ 1`, with `‖z‖ = 1` attained by some conjugate.

*References:*
- [Wikipedia: Salem number](https://en.wikipedia.org/wiki/Salem_number)

## Main definitions

* `IsSalem`: predicate asserting that a real number is a Salem number.
* `lehmerPolynomial`: Lehmer's degree-`10` reciprocal polynomial
  `X^10 + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1`.

## Main statements

* `IsPisot.not_isSalem`, `IsSalem.not_isPisot`: Pisot numbers and Salem numbers are disjoint.
* `not_isSalem_goldenRatio`: the golden ratio is not a Salem number.
* `Real.not_isSalem_intCast`: no rational integer is a Salem number.
* `mul_lehmerPolynomial_eq`: algebraic identity relating `lehmerPolynomial` to `X^3 - X - 1`.
-/

open Polynomial

/-- Predicate for **Salem numbers**: `τ > 1` is integral over `ℤ`, every root `z ≠ τ` of
`minpoly ℚ τ` in `ℂ` satisfies `‖z‖ ≤ 1`, and some root satisfies `‖z‖ = 1`. -/
def IsSalem (τ : ℝ) : Prop :=
  1 < τ ∧ IsIntegral ℤ τ ∧
    (∀ z ∈ (minpoly ℚ τ).aroots ℂ, z ≠ (τ : ℂ) → ‖z‖ ≤ 1) ∧
    ∃ z ∈ (minpoly ℚ τ).aroots ℂ, ‖z‖ = 1

namespace IsSalem

theorem one_lt {τ : ℝ} (h : IsSalem τ) : 1 < τ := h.1

theorem isIntegral {τ : ℝ} (h : IsSalem τ) : IsIntegral ℤ τ := h.2.1

end IsSalem

/-- Pisot–Vijayaraghavan numbers and Salem numbers are disjoint: every non-trivial conjugate of a
Pisot number lies strictly inside the unit disc, while `θ > 1` itself has norm `θ > 1`. -/
theorem IsPisot.not_isSalem {θ : ℝ} (h : IsPisot θ) : ¬ IsSalem θ := by
  rintro ⟨hgt1, _, _, z, hz, hnorm1⟩
  by_cases hzeq : z = (θ : ℂ)
  · rw [hzeq, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hnorm1
    linarith
  · have hlt : ‖z‖ < 1 := h.2.2 z hz hzeq
    linarith

/-- No Salem number is a Pisot–Vijayaraghavan number. -/
theorem IsSalem.not_isPisot {τ : ℝ} (h : IsSalem τ) : ¬ IsPisot τ :=
  fun hP => hP.not_isSalem h

/-- Because `Real.goldenRatio` is a Pisot–Vijayaraghavan number, it is not a Salem number. -/
theorem not_isSalem_goldenRatio : ¬ IsSalem Real.goldenRatio :=
  isPisot_goldenRatio.not_isSalem

namespace Real

/-- No real number `τ ≤ 1` is a Salem number. -/
theorem not_isSalem_of_le_one {τ : ℝ} (h : τ ≤ 1) : ¬ IsSalem τ :=
  fun hS => (not_lt_of_ge h) hS.1

/-- No rational integer `n : ℤ` is a Salem number, since its only complex conjugate over `ℚ` is `n`
itself. -/
theorem not_isSalem_intCast (n : ℤ) : ¬ IsSalem (n : ℝ) := by
  rintro ⟨hgt1, _, _, z, hz, hnorm1⟩
  rw [Polynomial.mem_aroots'] at hz
  have hdvd : minpoly ℚ (n : ℝ) ∣ (X - C (n : ℚ)) := by
    apply minpoly.dvd
    simp
  obtain ⟨g, hg⟩ := hdvd
  have hz1 : (aeval z) (X - C (n : ℚ)) = 0 := by
    rw [hg, map_mul, hz.2, zero_mul]
  have hzn : z = (n : ℂ) := by
    simp only [map_sub, aeval_X, aeval_C] at hz1
    exact sub_eq_zero.mp hz1
  rw [hzn, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hnorm1
  linarith

end Real

/-- Lehmer's degree-`10` reciprocal polynomial
`P(X) = X^10 + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1`. -/
noncomputable def lehmerPolynomial : ℤ[X] :=
  X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1

/-- Lehmer's decic arises from the plastic-ratio cubic `X^3 - X - 1` via
`(X - 1) * P(X) = X^8 * (X^3 - X - 1) + (X^3 + X^2 - 1)`. -/
theorem mul_lehmerPolynomial_eq :
    (X - 1) * lehmerPolynomial =
      X ^ 8 * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1) := by
  unfold lehmerPolynomial
  ring
