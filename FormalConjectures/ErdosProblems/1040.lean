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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1040

*Reference:* [erdosproblems.com/1040](https://www.erdosproblems.com/1040)

Let $F \subseteq \mathbb{C}$ be a closed infinite set, and let $\mu(F)$ be the infimum of
$|\{z : |f(z)| < 1\}|$ (Lebesgue measure), as $f$ ranges over all polynomials of
the shape $\prod(z - z_i)$ with $z_i \in F$.

Is $\mu(F) = 0$ whenever the transfinite diameter of $F$ is $\geq 1$?

The transfinite diameter (logarithmic capacity) of $F$ is defined by
$$\rho(F) = \lim_{n \to \infty} \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{1/\binom{n}{2}}.$$

Erdős, Herzog, and Piranian showed the answer is yes when $F$ is a line segment
or disc.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. **6** (1958), 125–148.
-/

open scoped ENNReal

open MeasureTheory Classical Filter Finset

namespace Erdos1040

/-- The product of pairwise distances $\prod_{i<j} \|z_i - z_j\|$ for a tuple of
complex numbers. -/
noncomputable def pairwiseDistProd {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The $n$-th transfinite diameter of $F \subseteq \mathbb{C}$:
$d_n(F) = \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{2/(n(n-1))}$. -/
noncomputable def nthTransfiniteDiam (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of $F \subseteq \mathbb{C}$:
$\rho(F) = \lim_{n \to \infty} d_n(F)$. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam F n))

/-- The sublevel set measure $\mu(F, \mu)$: infimum of $\mu(\{z : \|f(z)\| < 1\})$ over
all monic polynomials with roots in $F$. Uses `Fin (n+1)` to ensure at least
one root. -/
noncomputable def sublevelMeasure (F : Set ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (z : Fin (n + 1) → ℂ) (_ : ∀ i, z i ∈ F),
    μ {w : ℂ | ‖(univ : Finset (Fin (n + 1))).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem 1040 [EHP58, p.135]:

Is it true that for every closed infinite set $F \subseteq \mathbb{C}$ with transfinite
diameter $\geq 1$, the infimum of the Lebesgue measure of $\{z : |f(z)| < 1\}$
over monic polynomials with all roots in $F$ is zero?
-/
@[category research open, AMS 28 30]
theorem erdos_1040 : answer(sorry) ↔
    ∀ (F : Set ℂ), IsClosed F → F.Infinite → transfiniteDiameter F ≥ 1 →
    ∀ (μ : Measure ℂ) [μ.IsAddHaarMeasure], sublevelMeasure F μ = 0 := by
  sorry

end Erdos1040
