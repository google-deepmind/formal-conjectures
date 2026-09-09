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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

@[expose] public section

/-!
# The two-torsion cubic of a Weierstrass curve

Basic facts about `WeierstrassCurve.twoTorsionPolynomial`, the cubic
$4x^3 + b_2 x^2 + 2 b_4 x + b_6$ obtained by completing the square in the Weierstrass equation:
its evaluation, and — over a ring in which $4 \neq 0$ — that it really is a cubic.
-/

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The two-torsion cubic is $4x^3 + b_2 x^2 + 2 b_4 x + b_6$. -/
lemma eval_toPoly_twoTorsionPolynomial (x : R) :
    W.twoTorsionPolynomial.toPoly.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [twoTorsionPolynomial, Cubic.toPoly]

variable [NeZero (4 : R)]

lemma toPoly_twoTorsionPolynomial_ne_zero : W.twoTorsionPolynomial.toPoly ≠ 0 :=
  Cubic.ne_zero_of_a_ne_zero four_ne_zero

@[simp]
lemma natDegree_toPoly_twoTorsionPolynomial : W.twoTorsionPolynomial.toPoly.natDegree = 3 :=
  Cubic.natDegree_of_a_ne_zero four_ne_zero

@[simp]
lemma leadingCoeff_toPoly_twoTorsionPolynomial : W.twoTorsionPolynomial.toPoly.leadingCoeff = 4 :=
  Cubic.leadingCoeff_of_a_ne_zero four_ne_zero

end WeierstrassCurve
