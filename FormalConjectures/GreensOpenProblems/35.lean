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
- [Gr01] B. J. Green, *The number of squares and $B_h[g]$-sets*, Acta Arith. 100 (2001), no. 4,
  365-390.
- [CS17] A. Cloninger and S. Steinerberger, *On suprema of autoconvolutions with an application to
  Sidon sets*, Proc. Amer. Math. Soc. 145 (2017), no. 8, 3191-3200.
- [MV10] M. Matolcsi and C. Vinuesa, *Improved bounds on the supremum of autoconvolutions*,
  J. Math. Anal. Appl. 372 (2010), 439-447.
-/

namespace Green35

open MeasureTheory
open scoped Convolution ENNReal

/-- A nonnegative integrable function on $[0,1]$ with total integral $1$. -/
def IsUnitIntervalDensity (f : ℝ → ℝ) : Prop :=
  Integrable f ∧ (∀ x, 0 ≤ f x) ∧ Function.support f ⊆ Set.Icc (0 : ℝ) 1 ∧ (∫ x, f x) = 1

/-- The infimum of $\|f \ast f\|_p$ over unit-interval densities. -/
noncomputable def c (p : ℝ≥0∞) : ℝ≥0∞ :=
  sInf { r | ∃ f, IsUnitIntervalDensity f ∧ r = eLpNorm (f ⋆ f) p }

/-- Estimate $c(p)$ for $1 < p \le \infty$. -/
@[category research open, AMS 26 28 42]
theorem green_35 {p : ℝ≥0∞} (hp : 1 < p) :
    c p = answer(sorry) := by
  sorry

/-! Known bounds and comparisons. -/
namespace variants

/-- Lower bound for $c(2)$ from Green's first paper ([Gr01]). -/
@[category research solved, AMS 26 28 42]
theorem p2_lower : .ofReal 0.7559 ≤ c 2 := by
  sorry

/-- Best-known lower bound for $c(\infty)$ due to Cloninger and Steinerberger ([CS17]). -/
@[category research solved, AMS 26 28 42]
theorem pInf_lower : .ofReal 0.64 ≤ c ∞ := by
  sorry

/-- Best-known upper bound for $c(\infty)$ due to Matolcsi and Vinuesa ([MV10]). -/
@[category research solved, AMS 26 28 42]
theorem pInf_upper : c ∞ ≤ .ofReal 0.7505 := by
  sorry

/-- A comparison bound from Young's inequality. -/
@[category research solved, AMS 26 28 42]
@[category undergraduate, AMS 26 28 42]
theorem pInf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  sorry

end variants

end Green35
