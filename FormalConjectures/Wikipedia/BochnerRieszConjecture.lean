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
extends to a bounded operator in $L^p({\mathbb{R}^n})$ for $1<p<\infty$ if
$\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$. Since the Schwartz space is dense in $L^p({\mathbb{R}^n})$
for $1<p<\infty$, then it suffices to prove that it is bounded operator for such functions.
The cases $n=1$, $n=2$ have already been solved.

*Reference:* [source](https://en.wikipedia.org/wiki/Bochner%E2%80%93Riesz_mean)
-/

@[expose] public section

namespace BochnerRiesz

open scoped SchwartzMap
open FourierTransform
open MeasureTheory
open Complex


/--Bochner-Riesz multiplier definition $\xi \mapsto (1 - |\xi|^2)_+^\delta$ -/
noncomputable def BochnerRieszSymbol {n : ℕ} (δ : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
    if ‖ξ‖ < 1 then ((1 - ‖ξ‖^2)).rpow δ else 0

/--Test for the case $\delta=0$-/
@[category test, AMS 42]
lemma BochnerRieszSymbolZero (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    BochnerRieszSymbol 0 ξ = if ‖ξ‖ < 1 then 1 else 0 := by
    simp [BochnerRieszSymbol]


/--
Bochner-Riesz mean of a Schwartz function defined as
$B_\delta f(x) = \int_{\mathbb{R}^n} e^{2\pi i x\cdot\xi} (1 - |\xi|^2)_+^\delta
\widehat{f}(\xi)d\xi$ for a Schwartz map $f: {\mathbb{R}^n} \to \mathbb{C}$.
-/
noncomputable def BochnerRieszMean {n : ℕ} (δ : ℝ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :=
    (fun x : (EuclideanSpace ℝ (Fin n)) =>
    ∫ ξ, (𝓕 f ξ)  * (BochnerRieszSymbol δ ξ) * exp (2 * Real.pi * I * (x ⬝ᵥ ξ)))

/--
Bochner-Riesz conjecture.
For $3\le n$, $1<p<\infty$, and $\delta > \max\{0, n|1/2 - 1/p|- 1/2\}$,  there is a constant
$C > 0$, such that for any Schwartz map $f: {\mathbb{R}^n} \to \mathbb{C}$, we have
$\|B_\delta f(x)\|_{L^p} \le C\|f(x)\|_{L^p}$.
-/
@[category research open, AMS 42]
theorem BochnerRieszConjecture {n : ℕ} {δ : ℝ} {p : NNReal} (hp : 1 < p)
  (hn : 3 ≤ n) (hδ : δ > max (n * |1/2 - 1/(p:ℝ)| - 1/2) 0) :
  ∃ C : NNReal, C > 0 ∧ ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
  eLpNorm (BochnerRieszMean δ f) p ≤ C * eLpNorm f p :=
  sorry

end BochnerRiesz
