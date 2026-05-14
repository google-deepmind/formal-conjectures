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
# Convergence of the Borwein Series with Sinusoidal Coefficient

*References:*
- [MathWorld, Harmonic Series](https://mathworld.wolfram.com/HarmonicSeries.html)
- Borwein, J.; Bailey, D.; Girgensohn, R. *Experimentation in Mathematics: Computational Paths
  to Discovery*, A K Peters, 2004, p. 56.
-/

namespace BorweinSineSeries

/--
Does the series
$$
  \sum_{n=1}^{\infty} \frac{\left(\frac{2}{3} + \frac{1}{3}\sin n\right)^n}{n}
$$
converge?

After computing approximately $10^7$ terms, the partial sums approximate $2.163$.

See https://arxiv.org/abs/2007.11017 for a proof of the convergence,
relying on an irrationality measure for pi.

Also see
https://github.com/AxiomMath/gdm-formal-conjectures/blob/main/docs/BorweinSineSeries.md
for a partial formalization of the conjecture,
conditional on such an irrationality measure of pi (cf https://arxiv.org/abs/1912.06345).
-/
@[category research solved, formal_proof using lean4 at "https://github.com/AxiomMath/gdm-formal-conjectures/blob/main/BorweinSineSeries/solution.lean",  AMS 26 40]
theorem borwein_sine_series :
    answer(sorry) ↔
      Summable fun n : ℕ+ ↦ ((2 / 3 + 1 / 3 * Real.sin (n : ℝ)) ^ (n : ℕ)) / (n : ℝ) := by
  sorry

end BorweinSineSeries
