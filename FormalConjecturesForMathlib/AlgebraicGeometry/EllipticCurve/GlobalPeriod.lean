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

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public noncomputable section

/-!
# The real and complex periods of an elliptic curve as integrals

Let $E$ be an elliptic curve with Weierstrass equation
$y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ and invariant differential
$\omega = \frac{dx}{2y + a_1 x + a_3}$. Completing the square,
$(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6 =: F(x)$, the *2-division polynomial*
`WeierstrassCurve.Ψ₂Sq`, so $|\omega| = |dx| / \sqrt{|F(x)|}$ on the $x$-line.

* Over $\mathbb{R}$ (a curve `W : WeierstrassCurve ℝ`), the real locus $E(\mathbb{R})$ lies over
  $\{F \geq 0\}$ with two branches $2y + a_1 x + a_3 = \pm\sqrt{F(x)}$, so the real period is
  $\Omega_{\mathbb{R}} = \int_{E(\mathbb{R})} |\omega| = 2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$
  (`WeierstrassCurve.realPeriod`).
* Over $\mathbb{C}$ (a curve `W : WeierstrassCurve ℂ`), the $x$-coordinate is a double cover
  $E(\mathbb{C}) \to \mathbb{P}^1(\mathbb{C})$ and $|\omega \wedge \bar\omega| = 4\, dA(x) / |F(x)|$
  on each sheet, so the complex period is
  $\Omega_{\mathbb{C}} = \int_{E(\mathbb{C})} |\omega \wedge \bar\omega|
  = 4 \int_{\mathbb{C}} dA(x) / |F(x)|$ (`WeierstrassCurve.complexPeriod`).

*References:*
- [LMFDB](https://beta.lmfdb.org/knowledge/show/ec.period), knowl `ec.period`
- [Sil09] Silverman, J. H., *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in
  Mathematics 106, Springer, 2009. Chapter III §1 (Weierstrass equations, the invariant
  differential) and Chapter VI (elliptic curves over $\mathbb{C}$).
-/

namespace WeierstrassCurve

section Real

variable (W : WeierstrassCurve ℝ)

/-- The density $|\omega| / dx = 1 / \sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}$ of the invariant
differential on either branch of the real locus, as a function on $\mathbb{R}$, with the junk value
$0$ where the cubic is not positive. -/
def realPeriodIntegrand (x : ℝ) : ℝ := (√(W.Ψ₂Sq.eval x))⁻¹

/-- **The real period as an integral**: the integral of $|\omega|$ over the real locus
$E(\mathbb{R})$, that is $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$ with the integrand taken to be
$0$ where $F \leq 0$. This is the real period of the Birch and Swinnerton-Dyer conjecture, in the
convention that absorbs the real Tamagawa number. -/
def realPeriod : ℝ := 2 * ∫ x, W.realPeriodIntegrand x

end Real

section Complex

variable (W : WeierstrassCurve ℂ)

/-- The density of $\Omega_{\mathbb{C}}$ on the $x$-line: $1 / |\Psi_2^2(x)|$. -/
def complexPeriodIntegrand (x : ℂ) : ℝ := ‖W.Ψ₂Sq.eval x‖⁻¹

/-- **The complex period as an integral**: $\Omega_{\mathbb{C}}(E) = \int_{E(\mathbb{C})}
|\omega \wedge \bar\omega| = 4 \int_{\mathbb{C}} dA(x) / |\Psi_2^2(x)|$. Source: LMFDB knowl
`ec.period`. -/
def complexPeriod : ℝ := 4 * ∫ x : ℂ, W.complexPeriodIntegrand x

end Complex

end WeierstrassCurve
