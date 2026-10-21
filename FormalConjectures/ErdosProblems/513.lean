/-
Copyright 2025 The Formal Conjectures Authors.

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

public import FormalConjecturesUtil
public import FormalConjecturesForMathlib.Algebra.Polynomial.Algebra

/-!
# Erdős Problem 513

*Reference:*
 - [erdosproblems.com/513](https://www.erdosproblems.com/513)
 - [ClHa64] Clunie, J. and Hayman, W. K., The maximum term of a power series. J. Analyse Math.
  (1964), 143-186.
 - [Tao's optimization constant 51a](https://teorth.github.io/optimizationproblems/constants/51a.html)
-/

@[expose] public section

open scoped Nat Real
open Filter Polynomial

namespace Erdos513

noncomputable def ratio (r : ℝ) (f : ℂ → ℂ) : ℝ :=
  (⨆ n, ‖iteratedDeriv n f 0 * (n ! : ℝ)⁻¹ * r ^ n‖) / (⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖)

/-- The **Erdős maximum term constant** $B$: the supremum, over all transcendental entire
functions $f$, of $\liminf_{r \to \infty} \mu(r, f) / M(r, f)$. Here $\mu(r, f)$ is the maximum
term of the power series of $f$ on $|z| = r$, and $M(r, f) = \max_{|z| = r} |f(z)|$. -/
@[optimization_constant "51a"]
noncomputable def maxTermConstant : ℝ :=
  ⨆ f : {f : ℂ → ℂ // Transcendental ℂ[X] f ∧ Differentiable ℂ f},
    liminf (fun r : ℝ => ratio r f) atTop

def erdos_513.answer : ℝ := sorry

/-- Let `f` be a transcendental entire function. What is the greatest possible value of
`liminf (fun r : ℝ => ratio r f) atTop`? -/
@[category research open, question value, AMS 30]
theorem erdos_513 : maxTermConstant = erdos_513.answer := by
  sorry

/-- There is `c > 0` such that `maxTermConstant ≤ 2 / π - c`. This is proved in [ClHa64]. -/
@[category research solved, AMS 30]
theorem erdos_513.variants.upper_bound : ∃ c > 0, maxTermConstant ≤ 2 / π - c := by
  sorry

/-- `maxTermConstant > 1 / 2`: there is a transcendental entire `f` with
`liminf (fun r : ℝ => ratio r f) atTop > 1 / 2`. This was observed by Kövári (unpublished), and
[ClHa64] proves the stronger bound `> 4 / 7`. It does not hold for every `f`: for `f = exp` the
`liminf` is `0`. -/
@[category research solved, AMS 30]
theorem erdos_513.variants.lower_bound : maxTermConstant > 1 / 2 := by
  sorry

end Erdos513
