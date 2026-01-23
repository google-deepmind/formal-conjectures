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

We model a function `f : [0,1] → ℝ≥0` as a function on the subtype `Set.Icc (0 : ℝ) 1`, and
extend by `0` to a function on `ℝ` when forming convolutions.

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
open scoped Convolution

/-- Extend a function on `[0,1]` by zero to a function on `ℝ`. -/
def extendByZero (f : Set.Icc (0 : ℝ) 1 → ℝ≥0) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then (f ⟨x, hx⟩ : ℝ) else 0

/-- A nonnegative integrable function on `[0,1]` with total integral `1`. -/
def IsUnitIntervalDensity (f : Set.Icc (0 : ℝ) 1 → ℝ≥0) : Prop :=
  Integrable (extendByZero f) ∧
    (∫ x, extendByZero f x) = 1

/-- The class `F` of unit-interval densities. -/
def F : Set (Set.Icc (0 : ℝ) 1 → ℝ≥0) :=
  { f | IsUnitIntervalDensity f }

/-- A density for which the self-convolution is defined everywhere. -/
def IsAdmissible (f : Set.Icc (0 : ℝ) 1 → ℝ≥0) : Prop :=
  f ∈ F ∧
    ConvolutionExists (extendByZero f) (extendByZero f) (ContinuousLinearMap.lsmul ℝ ℝ)

/-- Convolution of two real-valued functions on `ℝ` with respect to Lebesgue measure. -/
noncomputable def convolution (f g : Set.Icc (0 : ℝ) 1 → ℝ≥0) : ℝ → ℝ :=
  extendByZero f ⋆ extendByZero g

/-- The infimum of `‖f ∗ f‖_p` over `f ∈ F`, where `F` is the unit-interval density class. -/
noncomputable def c (p : ℝ≥0∞) : ℝ≥0∞ :=
  sInf { r | ∃ f, IsAdmissible f ∧ r = eLpNorm (convolution f f) p }

/-- Estimate `c p` for `1 < p ≤ ∞`. -/
@[category research open, AMS 26 28 42]
theorem green_35 (p : ℝ≥0∞) (hp : 1 < p) :
    c p = answer(sorry) := by
  sorry

/-! Known bounds and comparisons. -/
namespace variants

/-- Lower bound for `c 2` from Green's first paper ([Gr01]). -/
@[category research solved, AMS 26 28 42]
theorem p2_lower : ENNReal.ofReal 0.7559 ≤ c 2 := by
  sorry

/-- Best-known lower bound for `c ∞` due to Cloninger and Steinerberger ([CS17]). -/
@[category research solved, AMS 26 28 42]
theorem pInf_lower : ENNReal.ofReal 0.64 ≤ c ∞ := by
  sorry

/-- Best-known upper bound for `c ∞` due to Matolcsi and Vinuesa ([MV10]). -/
@[category research solved, AMS 26 28 42]
theorem pInf_upper : c ∞ ≤ ENNReal.ofReal 0.7505 := by
  sorry

/-- A comparison bound from Young's inequality. -/
@[category research solved, AMS 26 28 42]
theorem pInf_lower_young : (c 2) ^ 2 ≤ c ∞ := by
  sorry

end variants

end Green35
