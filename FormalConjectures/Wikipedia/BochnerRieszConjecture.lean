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

public import FormalConjecturesUtil



/-!
# Bochner-Riesz conjecture

Given $\delta\in\mathbb{R}$, the Bochner-Riesz Mean is defined as
$B_\delta f(x) = \int_{\mathbb{R}^n} e^{2\pi i x\cdot\xi} (1 - |\xi|^2)_+^\delta
\widehat{f}(\xi)d\xi$ for a Schwartz function $f: {\mathbb{R}^n} \to \mathbb{C}$.
The Bochner-Riesz conjecture states that this
extends to a bounded operator in $L^p({\mathbb{R}^n})$ for $1<p<\infty$ if and only if
$\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$.
It is known that $\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$ implies $L^p$-boundedness, so only
the other direction is stated in here. Since the Schwartz space is dense in $L^p({\mathbb{R}^n})$
for $1<p<\infty$, then it suffices to prove that it is bounded operator for such functions.
The cases $n=1$, $n=2$ have already been solved, and [OpenAI](https://github.com/openai/math/tree/main/preprints/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026)
claims to have solved case $n=3$.

*Reference:* [source](https://en.wikipedia.org/wiki/Bochner%E2%80%93Riesz_mean)
-/

@[expose] public section

namespace BochnerRiesz

open scoped SchwartzMap
open scoped InnerProductSpace
open FourierTransform
open MeasureTheory
open Complex

/--Bochner-Riesz multiplier definition $\xi \mapsto (1 - |\xi|^2)_+^\delta$ -/
noncomputable def bochnerRieszSymbol {n : ℕ} (δ : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
    if ‖ξ‖ < 1 then ((1 - ‖ξ‖^2) ^ δ : ℝ) else 0

/--Test for the case $\delta=0$-/
@[category test, AMS 42]
lemma bochnerRieszSymbol_zero (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    bochnerRieszSymbol 0 ξ = if ‖ξ‖ < 1 then 1 else 0 := by
    simp [bochnerRieszSymbol]

/--
Bochner-Riesz mean of a Schwartz function defined as
$B_\delta f(x) = \int_{\mathbb{R}^n} e^{2\pi i x\cdot\xi} (1 - |\xi|^2)_+^\delta
\widehat{f}(\xi)d\xi$ for a Schwartz map $f: {\mathbb{R}^n} \to \mathbb{C}$.
-/
noncomputable def bochnerRieszMean {n : ℕ} (δ : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :=
    (fun x : (EuclideanSpace ℝ (Fin n)) =>
    ∫ ξ, (𝓕 f ξ)  * (bochnerRieszSymbol δ ξ) * exp (2 * Real.pi * I * ⟪x, ξ⟫_ℝ))

/--
Bochner-Riesz conjecture.
For $4\le n$, $1<p<\infty$, and $\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$,  there is a constant
$C > 0$, such that for any Schwartz map $f: {\mathbb{R}^n} \to \mathbb{C}$, we have
$\|B_\delta f(x)\|_{L^p} \le C\|f(x)\|_{L^p}$.
-/
@[category research open, AMS 42]
theorem bochner_riesz_conjecture {n : ℕ} {δ : ℝ} {p : NNReal} (hp : 1 < p)
  (hn : 4 ≤ n) (hδ : δ > max (n * |1/2 - 1/(p:ℝ)| - 1/2) 0) :
  ∃ C : NNReal, C > 0 ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
  eLpNorm (bochnerRieszMean δ f) p ≤ C * eLpNorm f p := by sorry

/--
Bochner-Riesz conjecture.
For $1<p<\infty$, and $\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$, there is a constant
$C > 0$, such that for any Schwartz map $f: {\mathbb{R}^3} \to \mathbb{C}$, we have
$\|B_\delta f(x)\|_{L^p} \le C\|f(x)\|_{L^p}$. This has been claimed by [OpenAI](https://github.com/openai/math/tree/main/preprints/Bochner-Riesz-Multipliers-in-Three-Dimensions-September-24-2026)
-/
@[category research open, AMS 42]
theorem bochner_riesz_conjecture₃ {δ : ℝ} {p : NNReal} (hp : 1 < p)
  (hδ : δ > max (3 * |1/2 - 1/(p:ℝ)| - 1/2) 0) :
  ∃ C : NNReal, C > 0 ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ,
  eLpNorm (bochnerRieszMean δ f) p ≤ C * eLpNorm f p := by sorry



end BochnerRiesz
