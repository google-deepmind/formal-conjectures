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
# Erdős Problem 1002

*Reference:* [erdosproblems.com/1002](https://www.erdosproblems.com/1002)

For any $0 < \alpha < 1$, let
$$f(\alpha, n) = \frac{1}{\log n} \sum_{1 \le k \le n} \left(\frac{1}{2} - \{\alpha k\}\right)$$
where $\{\cdot\}$ denotes the fractional part.

Does $f(\alpha, n)$ have an asymptotic distribution function? In other words, is there
a non-decreasing function $g$ such that $g(-\infty) = 0$, $g(\infty) = 1$, and
$$\lim_{n \to \infty} |\{\alpha \in (0,1) : f(\alpha,n) \le c\}| = g(c)$$
where $|\cdot|$ denotes Lebesgue measure?

Kesten [Ke60] proved the analogous result with an additional shift $\beta$:
if $f(\alpha, \beta, n) = \frac{1}{\log n} \sum_{k=1}^n \left(\frac{1}{2} - \{\beta + \alpha k\}\right)$,
then $f(\alpha, \beta, n)$ has asymptotic distribution function
$g(c) = \frac{1}{\pi} \int_{-\infty}^{\rho c} \frac{1}{1+t^2} \, dt$
where $\rho > 0$ is an explicit constant.
-/

open Finset Filter MeasureTheory

namespace Erdos1002

/-- The function $f(\alpha, n) = \frac{1}{\log n} \sum_{k=1}^{n} \left(\frac{1}{2} - \{\alpha k\}\right)$,
where $\{\cdot\}$ denotes the fractional part. -/
noncomputable def erdosF (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2 - Int.fract (α * ↑k))) / Real.log ↑n

/--
Erdős Problem 1002 [Er64b]:

Does the function $f(\alpha, n) = \frac{1}{\log n} \sum_{k=1}^n \left(\frac{1}{2} - \{\alpha k\}\right)$
have an asymptotic distribution function? That is, is there a non-decreasing function
$g : \mathbb{R} \to \mathbb{R}$ with $g(-\infty) = 0$ and $g(\infty) = 1$ such that for every
$c \in \mathbb{R}$,
$$\lim_{n \to \infty} \mu(\{\alpha \in (0,1) : f(\alpha,n) \le c\}) = g(c)$$
where $\mu$ is Lebesgue measure.
-/
@[category research open, AMS 11 28]
theorem erdos_1002 : answer(sorry) ↔
    ∃ g : ℝ → ℝ, Monotone g ∧
    Filter.Tendsto g Filter.atBot (nhds 0) ∧
    Filter.Tendsto g Filter.atTop (nhds 1) ∧
    ∀ c : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        (volume (Set.Ioo (0 : ℝ) 1 ∩ {α : ℝ | erdosF α n ≤ c})).toReal)
      Filter.atTop (nhds (g c)) := by
  sorry

end Erdos1002
