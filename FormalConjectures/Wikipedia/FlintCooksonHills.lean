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
# Convergence of the Flint Hills and Cookson Hills series

*References:*
- [Wikipedia: Examples of numerical series](https://en.wikipedia.org/wiki/Series_(mathematics)#Examples_of_numerical_series)
- [MathWorld: Flint Hills Series](https://mathworld.wolfram.com/FlintHillsSeries.html)
- [Ale11] Alekseyev, *On convergence of the Flint Hills series*.
  [arXiv:1104.5100](https://arxiv.org/abs/1104.5100)
- [Mei22] Meiburg, *Bounds on irrationality measures and the Flint-Hills series*.
  [arXiv:2208.13356](https://arxiv.org/abs/2208.13356)
- [MathWorld: Cookson Hills Series](https://mathworld.wolfram.com/CooksonHillsSeries.html)
- [OAI26] OpenAI, *The irrationality exponent of $\pi$ is 2*. OpenAI Math Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf
-/

@[expose] public section

namespace FlintCooksonHills

/--
The Flint Hills series summing $csc(n)^2 / n^3$ from $n=1$ to $\infty$ converges.
(Note that we 0-index the series below.)

Alekseyev [Ale11, Corollary 4] showed that convergence implies that the irrationality measure
$\mu(\pi)$ is at most $5/2$; conversely, Meiburg [Mei22] showed that the series converges if
$\mu(\pi) < 5/2$. OpenAI [OAI26] proved that $\mu(\pi) = 2$, and proved convergence in Lean.
-/
@[category research solved, question, AMS 40]
theorem flint_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.sin (n + 1)^2))) := by
  sorry

/-- OpenAI's Lean statement, with the index cast from `ℕ`, gives
`flint_hills_series_converges`. -/
@[category test, AMS 40]
theorem flint_hills_series_converges_of_natCast
    (h : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * Real.sin (n + 1 : ℕ) ^ 2))) :
    type_of% flint_hills_series_converges := by
  simpa using h

/--
The Cookson Hills series summing $sec(n)^2 / n^3$ from $n=1$ to $\infty$ converges.
-/
@[category research open, question, AMS 40]
theorem cookson_hills_series_converges :
    Summable (fun n : ℕ =>
      1 / ((((n + 1) : ℝ)^3) * (Real.cos (n + 1)^2))) := by
  sorry

end FlintCooksonHills
