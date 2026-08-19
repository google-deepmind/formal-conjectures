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

import FormalConjectures.Other.CaratheodoryLoewner

/-!
# The announced smooth counterexamples to the Carathéodory and Loewner conjectures

This file begins the formalisation of the explicit family from the recent announcement quoted
in the issue or pull request associated with this file. It records the planar formula and states
its smoothness and index properties. The global interpretation of `counterexample 2` as a support
function on the two-sphere is left for a subsequent step.

The exact public URL, author, and date of the announcement should be added here before submission.
-/

open scoped ContDiff

namespace CaratheodoryLoewner

/-- The periodic real-valued function used in the announced counterexample. -/
noncomputable def counterexampleSeed (z : ℂ) : ℝ :=
  -Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
    Real.cos (4 * z.im) / 32 + Real.sin z.re * Real.sin z.im

/-- The announced family `g_k` of smooth functions on the complex plane.

The use of the principal complex power chooses a square-root branch when `k` is odd. The seed is
even, so the resulting real-valued expression is independent of the sign of that square root. -/
noncomputable def counterexample (k : ℕ) (z : ℂ) : ℝ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
      counterexampleSeed w / (1 + r ^ 2) + 10 ^ 10

/-- Each member of the announced family is smooth on the whole complex plane, including at the
origin. The flat exponential factor is essential at the origin. -/
@[category research solved, AMS 26 53]
theorem counterexample_contDiff (k : ℕ) : ContDiff ℝ ∞ (counterexample k) := by
  sorry

/-- For positive `k`, the origin is an isolated umbilic of principal-line index `1 + k / 2`.

`HasIsolatedZeroIndex` stores twice the principal-line index, hence the integer `2 + k` here. -/
@[category research solved, AMS 26 53 57]
theorem counterexample_hasIsolatedZeroIndex (k : ℕ) (hk : 0 < k) :
    HasIsolatedZeroIndex (traceFreeHessian (counterexample k)) 0 (2 + k) := by
  sorry

/-- Every positive member with `k > 0` violates the index bound in the smooth Loewner
conjecture. -/
@[category research solved, AMS 53 57]
theorem counterexample_not_loewner_bound (k : ℕ) (hk : 0 < k) :
    ¬ ((2 + k : ℕ) : ℤ) ≤ 2 := by
  omega

end CaratheodoryLoewner
