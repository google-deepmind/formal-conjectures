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

import FormalConjectures.Util.ProblemImports

open Topology Filter Real unitInterval Polynomial

/-!
# Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators

*References:*

* [A problem in Constructive theory of functions, Szopol 2010](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf?utm_source=perplexity)

The Bézier-type Bernstein operators $B_{n,\alpha}$ for $\alpha > 0$ are defined for
$f : [0,1] \to \mathbb{R}$ by
\[
(B_{n,\alpha} f)(x)
  = \sum_{k=0}^n f\!\left(\frac{k}{n}\right)
    \left( J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha} \right),
\]
where
\[
J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x),
\qquad
p_{n,j}(x) = \binom{n}{j} x^j(1-x)^{n-j},
\]
and $J_{n,n+1}(x) = 0$.

In the classical case $\alpha = 1$, these operators reduce to the usual Bernstein operators.
For sufficiently smooth $f$, one has the classical Voronovskaja asymptotic formula
\[
\lim_{n \to \infty} n\bigl( B_{n,1} f(x) - f(x) \bigr)
    = \tfrac{1}{2} x(1-x) f''(x).
\]

## Known Results
* For $\alpha = 1$, the asymptotics are completely understood.
* Numerical experiments indicate that for $\alpha \neq 1$ the quantity
    \[
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr)
    \]
    may converge to a non-zero limit.

## The Problem
Determine the asymptotic behaviour of the Bézier-type Bernstein operators for $\alpha \neq 1$:
\textbf{Existence of the limit:}
    Prove (or disprove) the existence of the limit
    \[
        \lim_{n \to \infty}
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr),
    \]
    at least for functions $f$ that are twice differentiable at $x \in (0,1)$.
    \item \textbf{Explicit form of the limit:}
    If the limit exists, determine an explicit expression for it in terms of $f$, $x$, and $\alpha$.
-/

/--
Cumulative sum `J_{n,k}(x) = ∑_{j=k}^n p_{n,j}(x)`
-/
noncomputable def BernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n,
    bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
`(B_{n,α} f)(x) = ∑_{k=0}^n f(k/n) * (J_{n,k}(x)^α - J_{n,k+1}(x)^α)`
-/
noncomputable def BezierBernstein (n : ℕ) (α : ℝ) (f : ℝ  → ℝ) (x : ℝ) : ℝ :=
∑ k ∈  Finset.range (n+1),
    f (k/n) * (((BernsteinTail n k).eval x) ^ α - ((BernsteinTail n k + 1).eval x) ^ α)

/--
Classical Voronovskaja theorem (α = 1)

For smooth `f`, the limit:
    n * (B_n f x - f x) → (1/2)*x*(1-x)*f''(x)

This is already in the literature; here we state it.
-/
@[category research solved, AMS 26 40 47]
theorem voronovskaja_theorem.bernstein_operators
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (f'' : ℝ := iteratedDerivWithin 2 f I x) :
    Tendsto (fun (n : ℕ) => n • (BezierBernstein n 1 f x - f x))
    atTop
    (𝓝 ((1/2) * x * (1-x) * f'')) := by
  sorry

/--
Conjecture: Voronovskaja-type formula for Bézier-Bernstein operators
with shape parameter α ≠ 1.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (f'' : ℝ := iteratedDerivWithin 2 f I x)
    (x : ℝ)(hf : ContDiffAt ℝ 2 f x) : ∃ L : ℝ,
    Tendsto (fun n : ℕ => Real.sqrt n * (BezierBernstein n α f x - f x)) atTop (𝓝 L) := by
  sorry
