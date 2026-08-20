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

import FormalConjecturesUtil

/-!
# Loewner's conjecture

Loewner's conjecture says that an isolated umbilic point of a sufficiently smooth surface has
principal-line index at most one. We state the now-disproved smooth version for functions and the
classical positive result for real-analytic functions. Levent Alpöge announced the smooth
counterexample on 19 August 2026.

*References:*
- [M. Ghomi, *Open Problems in Geometry of Curves and Surfaces*, Problem
  8.2](https://ghomi.math.gatech.edu/Papers/op.pdf)
- [C. J. Titus, *A proof of a conjecture of Loewner and of the conjecture of Carathéodory on
  umbilic points*](https://doi.org/10.1007/BF02392036)
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/

open Metric
open scoped ContDiff

namespace LoewnerConjecture

/-- The trace-free part of the Hessian of `f : ℂ → ℝ`, encoded as a complex number.

Its zeros are precisely the points where the two eigendirections of the Hessian are not
distinct. The argument of this complex number is twice the angle of a principal line. -/
noncomputable def traceFreeHessian (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  let H := fderiv ℝ (fun w ↦ fderiv ℝ f w) z
  (H 1 1 - H Complex.I Complex.I : ℝ) + (2 * H 1 Complex.I : ℝ) * Complex.I

/-- A complex-valued function `q` has an isolated zero at `z` with winding number `m`.

The lift `θ` records the argument of `q` on a sufficiently small positively oriented circle.
For a trace-free Hessian, the corresponding principal-line index is `m / 2`. -/
def HasIsolatedZeroIndex (q : ℂ → ℂ) (z : ℂ) (m : ℤ) : Prop :=
  ∃ ε > 0,
    q z = 0 ∧
      (∀ w, w ≠ z → dist w z < ε → q w ≠ 0) ∧
      ∃ r, 0 < r ∧ r < ε ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
          q (z + r * Complex.exp ((t : ℂ) * Complex.I)) /
            ‖q (z + r * Complex.exp ((t : ℂ) * Complex.I))‖) ∧
        θ (2 * Real.pi) - θ 0 = 2 * Real.pi * m

/-- Loewner's conjecture for functions of class `C^k` near an isolated umbilic. The integer `m`
is twice the principal-line index, so the bound `m ≤ 2` says that this index is at most one. -/
def LoewnerConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ (f : ℂ → ℝ) (z : ℂ) (m : ℤ), ContDiffAt ℝ k f z →
    HasIsolatedZeroIndex (traceFreeHessian f) z m → m ≤ 2

/-- **The smooth Loewner conjecture.**

The principal-line index at an isolated umbilic of a smooth Hessian was conjectured to be at most
one. Alpöge's smooth family gives isolated umbilics of larger index, so the answer is false. -/
@[category research solved, AMS 53 57,
  formal_proof using formal_conjectures at "https://github.com/google-deepmind/formal-conjectures/blob/150d2159bd37294ac7ad45c4ae7f199fb7dcd871/FormalConjectures/Other/CaratheodoryLoewnerCounterexample.lean#L53"]
theorem loewner_conjecture : answer(False) ↔ LoewnerConjectureOfClass ∞ := by
  sorry

/-- **The real-analytic Loewner conjecture.**

The principal-line index at an isolated umbilic of a real-analytic Hessian is at most one.
This is the classical result attributed to Hamburger and subsequently treated by Titus. -/
@[category research solved, AMS 53 57]
theorem loewner_conjecture_analytic : LoewnerConjectureOfClass ω := by
  sorry

end LoewnerConjecture
