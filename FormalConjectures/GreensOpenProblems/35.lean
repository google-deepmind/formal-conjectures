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

import FormalConjectures.Util.ProblemImports

/-!
# Ben Green's Open Problem 35

Estimate the infimum of the $L^p$ norm of the self-convolution of a nonnegative integrable
function supported on $[0,1]$ with total integral $1$.

We model a function `f : [0,1] → ℝ≥0` as a function `f : ℝ → ℝ` that is nonnegative, integrable,
supported on `[0,1]`, and has total integral `1`.

*References:*
- [Ben Green's Open Problem 35](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.35)
- [Gr01](https://people.maths.ox.ac.uk/greenbj/papers/number-of-squares-and-Bh%5Bg%5D.pdf)
  B. J. Green, *The number of squares and $B_h[g]$-sets*, Acta Arith. 100 (2001), no. 4, 365-390.
- [CS17](https://arxiv.org/abs/1403.7988)
  A. Cloninger and S. Steinerberger, *On suprema of autoconvolutions with an application to Sidon
  sets*, Proc. Amer. Math. Soc. 145 (2017), no. 8, 3191-3200.
- [MV10](https://arxiv.org/abs/0907.1379)
  M. Matolcsi and C. Vinuesa, *Improved bounds on the supremum of autoconvolutions*,
  J. Math. Anal. Appl. 372 (2010), 439-447.
-/

namespace Green35

open MeasureTheory
open scoped Convolution ENNReal

/-- A nonnegative integrable function on $[0,1]$ with total integral $1$. -/
def IsUnitIntervalDensity (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ (∀ x, 0 ≤ f x) ∧ Function.support f ⊆ .Icc (0 : ℝ) 1 ∧ ∫ x, f x = 1

/-- The infimum of $\|f \ast f\|_p$ over unit-interval densities. -/
noncomputable def c (p : ℝ≥0∞) : ℝ≥0∞ :=
  sInf { r | ∃ f, IsUnitIntervalDensity f ∧ r = eLpNorm (f ⋆ f) p }

/-- Lower bound for $c(p)$ for $1 < p \le \infty$, improving the known value at $p = 2$ or $p = \infty$. -/
@[category research open, AMS 26 28 42]
theorem green_35.lower :
    let lb : ℝ≥0∞ → ℝ≥0∞ := answer(sorry)
    (∀ p, 1 < p → lb p ≤ c p) ∧
      (ENNReal.ofReal (Real.sqrt (4 / 7)) < c 2 ∨ 0.64 < c ∞) := by
  sorry

/-- Upper bound for $c(p)$ for $1 < p \le \infty$, improving the best-known value at $p = \infty$. -/
@[category research open, AMS 26 28 42]
theorem green_35.upper :
    let ub : ℝ≥0∞ → ℝ≥0∞ := answer(sorry)
    (∀ p, 1 < p → c p ≤ ub p) ∧ ub ∞ < 0.7505 := by
  sorry

/-! Known bounds and comparisons. -/
namespace variants

/-- Lower bound for $c(2)$ from Green's first paper ([Gr01]); the constant is `sqrt(4/7)` (about 0.7559). -/
@[category research solved, AMS 26 28 42]
theorem c_2_lower : ENNReal.ofReal (Real.sqrt (4 / 7)) ≤ c 2 := by
  sorry

/-- Best-known lower bound for $c(\infty)$ due to Cloninger and Steinerberger ([CS17]). -/
@[category research solved, AMS 26 28 42]
theorem c_inf_lower : 0.64 ≤ c ∞ := by
  sorry

/-- Best-known upper bound for $c(\infty)$ due to Matolcsi and Vinuesa ([MV10]). -/
@[category research solved, AMS 26 28 42]
theorem c_inf_upper : c ∞ ≤ 0.7505 := by
  sorry

/-- A comparison bound from Young's inequality. -/
@[category undergraduate, AMS 26 28 42]
theorem c_inf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  sorry

end variants

end Green35
