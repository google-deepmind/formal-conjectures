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
import FormalConjectures.ErdosProblems.«1043»

/-!
# Erdős Problem 1048

*References:*
- [erdosproblems.com/1048](https://www.erdosproblems.com/1048)
- [EHP58] Erdős, P. and Herzog, F. and Piranian, G., *Metric properties of polynomials*.
  J. Analyse Math. (1958), 125-148.
- [Po61] Pommerenke, Ch., *On metric properties of complex polynomials*. Michigan Math. J.
  (1961), 97-115.
-/

namespace Erdos1048

open Polynomial Erdos1043

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert < 1\}$ -/
def openLevelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/--
If $f\in \mathbb{C}[x]$ is a monic polynomial with all roots satisfying
$\lvert z\rvert \leq r$ for some $r<2$, then must
\[\{ z: \lvert f(z)\rvert <1\}\]
have a connected component with diameter $>2-r$?

A problem of Erdős, Herzog, and Piranian [EHP58].

Pommerenke [Po61] proved the answer is no for $r>1$, showing that if $f(z)=z^n-r^n$ then
$\{ z: \lvert f(z)\rvert \leq 1\}$ has $n$ connected components, all with diameter
$\to 0$ as $n\to \infty$.
-/
@[category research solved, AMS 30]
theorem erdos_1048 : answer(False) ↔
    ∀ (r : ℝ) (f : ℂ[X]), r < 2 → f.Monic → f.degree ≥ 1 → (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
        Metric.ediam (connectedComponentIn (openLevelSet f) z) := by
  sorry

/--
Pommerenke [Po61] proved the answer is no for $r>1$, showing that if $f(z)=z^n-r^n$ then
$\{ z: \lvert f(z)\rvert \leq 1\}$ has $n$ connected components, all with diameter
$\to 0$ as $n\to \infty$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.pommerenke_ncard_components (r : ℝ) (hr : 1 < r) (n : ℕ) (hn : 1 ≤ n)
    (f : ℂ[X]) (hf : f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n)) :
    {C : Set ℂ | ∃ z ∈ levelSet f, C = connectedComponentIn (levelSet f) z}.ncard = n := by
  sorry

/--
Pommerenke [Po61] proved the answer is no for $r>1$, showing that if $f(z)=z^n-r^n$ then
$\{ z: \lvert f(z)\rvert \leq 1\}$ has $n$ connected components, all with diameter
$\to 0$ as $n\to \infty$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.pommerenke_diam_tendsto_zero (r : ℝ) (hr : 1 < r) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ f : ℂ[X], f = (X : ℂ[X]) ^ n - C ((r : ℂ) ^ n) →
      ∀ z ∈ levelSet f,
        Metric.ediam (connectedComponentIn (levelSet f) z) < ENNReal.ofReal ε := by
  sorry

/--
On the other hand, if $0<r\leq 1$, then the answer is yes, as also shown by Pommerenke [Po61].
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.r_le_one (r : ℝ) (hr₀ : 0 < r) (hr₁ : r ≤ 1) (f : ℂ[X])
    (hmonic : f.Monic) (hdeg : f.degree ≥ 1) (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r) :
    ∃ z ∈ openLevelSet f, ENNReal.ofReal (2 - r) <
      Metric.ediam (connectedComponentIn (openLevelSet f) z) := by
  sorry

/--
If $0\leq r\leq 1/2$ then the component which contains $0$ must have diameter $\geq 2$, which
$f(z)=z^n$ shows is best possible.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.diam_ge_two (r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 2) (f : ℂ[X])
    (hmonic : f.Monic) (hdeg : f.degree ≥ 1) (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r) :
    2 ≤ Metric.ediam (connectedComponentIn (levelSet f) 0) := by
  sorry

/--
If $0\leq r\leq 1/2$ then the component which contains $0$ must have diameter $\geq 2$, which
$f(z)=z^n$ shows is best possible.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.diam_ge_two_is_best (n : ℕ) (hn : 1 ≤ n) :
    Metric.ediam (connectedComponentIn (levelSet ((X : ℂ[X]) ^ n)) 0) = 2 := by
  sorry

/--
If $1/2<r\leq \frac{\sqrt{5}-1}{2}$ then the component which contains $0$ must have
diameter $>1/r$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.diam_gt_inv_r (r : ℝ) (hr₀ : 1 / 2 < r)
    (hr₁ : r ≤ (Real.sqrt 5 - 1) / 2) (f : ℂ[X]) (hmonic : f.Monic) (hdeg : f.degree ≥ 1)
    (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r) :
    ENNReal.ofReal (1 / r) < Metric.ediam (connectedComponentIn (levelSet f) 0) := by
  sorry

/--
If $\frac{\sqrt{5}-1}{2}\leq r\leq 1$ then the component which contains $0$ must have
diameter $>2-r^2$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.diam_gt_two_sub_sq (r : ℝ) (hr₀ : (Real.sqrt 5 - 1) / 2 ≤ r)
    (hr₁ : r ≤ 1) (f : ℂ[X]) (hmonic : f.Monic) (hdeg : f.degree ≥ 1)
    (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ r) :
    ENNReal.ofReal (2 - r ^ 2) < Metric.ediam (connectedComponentIn (levelSet f) 0) := by
  sorry

end Erdos1048
