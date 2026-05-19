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
For $f$ which are $C^2$ on $[0,1]$, one has the classical Voronovskaja
asymptotic formula
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
Determine the asymptotic behaviour of the Bézier-type Bernstein operators for $\alpha > 0$,
$\alpha \neq 1$:
\textbf{Existence of the limit:}
    Prove (or disprove) the existence of the limit
    \[
        \lim_{n \to \infty}
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr),
    \]
    at least for sufficiently smooth functions $f$.
    \textbf{Explicit form of the limit:}
    If the limit exists, determine an explicit expression for it in terms of $f$, $x$, and $\alpha$.

*References:*

* [Voronovskaja-type Formula for the Bézier Variant of the Bernstein Operators](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf),
  by *Ulrich Abel*, in *Constructive Theory of Functions, Sozopol 2010*.
-/

namespace VoronovskajaTypeFormula

/--
Cumulative sum $J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x)$.
-/
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
\[
(B_{n,\alpha} f)(x)
= \sum_{k=0}^{n}
f\!\left(\frac{k}{n}\right)
\left(
J_{n,k}(x)^{\alpha}
- J_{n,k+1}(x)^{\alpha}
\right)
\]
-/
noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (k / n) * ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

/--
Classical Voronovskaja theorem (α = 1).

For functions $f$ that are $C^2$ on $[0,1]$, the limit:
\[
n\bigl( B_n f(x) - f(x) \bigr)
\;\longrightarrow\;
\frac{1}{2}\, x(1 - x)\, f''(x)
\]
-/
@[category research solved, AMS 26 40 47]
theorem voronovskaja_theorem.bernstein_operators
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    let f'' : ℝ := iteratedDerivWithin 2 f I x
    Tendsto (fun (n : ℕ) => (n : ℝ) * (bezierBernstein n 1 f x - f x))
    atTop
    (𝓝 ((1 / 2) * x * (1 - x) * f'')) := by
  sorry

/--
Conjecture: Voronovskaja-type formula for Bézier-Bernstein operators
with shape parameter $\alpha > 0$, $\alpha \neq 1$.

The source asks for sufficiently smooth functions. This concrete version uses
`ContDiffOn ℝ 2 f I` as a readable baseline regularity assumption; since the
domain is the compact interval $[0,1]$, this also explains why no separate
boundedness assumption is included here. The variants below record the unknown
smoothness threshold more explicitly.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1)
    (f : ℝ → ℝ) (x : ℝ) (hx : x ∈ I)
    (hf : ContDiffOn ℝ 2 f I) :
    Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
      (𝓝 answer(sorry)) := by
  sorry

/--
Variant of the Bézier-Bernstein Voronovskaja problem which treats "sufficiently smooth" as an
eventual condition in the smoothness order $m$: for all sufficiently large finite $m$, every
$C^m$ function on $[0,1]$ should have the asserted asymptotic formula.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let limitFormula : (ℝ → ℝ) → ℝ → ℝ := answer(sorry)
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (limitFormula f x)) := by
  sorry

/--
Existence-only version of the eventual-smoothness variant. This separates the first part of the
source problem, proving that the scaled sequence has some limit, from the stronger task of finding
an explicit expression for that limit.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.eventually_smooth.limit_exists
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        ∃ L : ℝ,
          Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
            (𝓝 L) := by
  sorry

/--
Variant of the Bézier-Bernstein Voronovskaja problem with the required smoothness order itself
left as an answer. Replacing `(answer(sorry) : ℕ)` by a concrete value lets one state the
conjecture for a chosen regularity threshold.
-/
@[category research open, AMS 26 40 47]
theorem voronovskaja_theorem.bezier_bernstein_operators.variants.answer_smoothness
    (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    let m : ℕ := answer(sorry)
    let limitFormula : (ℝ → ℝ) → ℝ → ℝ := answer(sorry)
    ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
      Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
        (𝓝 (limitFormula f x)) := by
  sorry

end VoronovskajaTypeFormula
