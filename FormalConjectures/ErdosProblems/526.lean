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
# Erdős Problem 526

Dvoretzky's covering problem: given a sequence of arc lengths $a_n \to 0$ with $\sum a_n = \infty$,
arcs of these lengths placed independently and uniformly at random on the unit circle cover the
entire circle with probability one if and only if $\sum \exp(a_1+\cdots+a_n)/n^2 = \infty$.

*Reference:* [erdosproblems.com/526](https://www.erdosproblems.com/526)

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961),
p. 253.

[Dv56] Dvoretzky, A., _On covering a circle by randomly placed arcs_. Proc. Nat. Acad. Sci. U.S.A.
(1956), 199–203.

[Sh72] Shepp, L. A., _Covering the circle with random arcs_. Israel J. Math. 11 (1972), 328–345.
-/

open MeasureTheory ProbabilityTheory Filter Finset BigOperators Set

namespace Erdos526

/-- Point $y$ is covered by an arc of length $\ell$ starting at $x$ on the unit circle
$\mathbb{R}/\mathbb{Z}$. The clockwise arc-distance from $x$ to $y$ is the fractional
part of $(y - x)$. -/
noncomputable def CircArcCovers (x y ℓ : ℝ) : Prop :=
  Int.fract (y - x) < ℓ

/-- The full unit circle $[0,1)$ is covered by arcs starting at $\omega(n)$ of lengths $a(n)$. -/
noncomputable def CircleFullyCovered (ω a : ℕ → ℝ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → y < 1 → ∃ n : ℕ, CircArcCovers (ω n) y (a n)

/--
Dvoretzky's covering problem [Er61, p. 253] (solved by Shepp [Sh72]).

Let $a_n \geq 0$ with $a_n \to 0$ and $\sum a_n = \infty$. If we independently and uniformly
place random arcs of length $a_n$ on the unit circle, Shepp showed the circle is covered with
probability $1$ if and only if
$$
  \sum_n \frac{\exp(a_1 + \cdots + a_n)}{n^2} = \infty.
$$

The probability space $(\Omega, \mu)$ carries independent $\mathrm{Uniform}[0,1)$ random
variables $X(n)$ giving the starting point of the $n$-th arc.
-/
@[category research solved, AMS 60]
theorem erdos_526
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (a : ℕ → ℝ)
    (ha_nonneg : ∀ n, 0 ≤ a n)
    (ha_tendsto : Tendsto a atTop (nhds 0))
    (ha_diverges : ¬Summable a)
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ n, Measurable (X n))
    (hX_unif : ∀ n, Measure.map (X n) μ = volume.restrict (Ico (0 : ℝ) 1))
    (hX_indep : iIndepFun X μ) :
    (∀ᵐ ω ∂μ, CircleFullyCovered (fun n => X n ω) a) ↔
      ¬Summable (fun n => Real.exp (∑ i ∈ range (n + 1), a i) / ((n : ℝ) + 1) ^ 2) := by
  sorry

end Erdos526
