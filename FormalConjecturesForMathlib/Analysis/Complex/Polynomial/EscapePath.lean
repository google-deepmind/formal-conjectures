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

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.BoundedVariation

/-!
# Escape paths of unit-circle polynomials
-/

@[expose] public section

open Set

namespace Polynomial

/--
A polynomial `P` is *admissible* if `P(0) = 1`, `P` is nonconstant, and all its roots lie on the
unit circle.
-/
def IsNormalizedUnitCircle (P : ℂ[X]) : Prop :=
  P.eval 0 = 1 ∧ 0 < P.natDegree ∧ ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1

/--
`γ : [0, 1] → ℂ` is a path in `{z : |P(z)| < 1}` connecting `0` to the unit circle. Since
`|P(0)| = 1`, the strict inequality is only required away from the starting point.
-/
def IsEscapePath (P : ℂ[X]) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
    ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1

end Polynomial
