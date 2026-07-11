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
# Asymptotic density of powerful numbers

Let $Q(x)$ denote the number of powerful integers up to $x$. Erdős and Szekeres [ES35] proved
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + O(x^{1/3}),$$
and Bateman and Grosswald [BG58] sharpened this to
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} + O(x^{1/6}).$$
Improving the exponent $1/6$ in the error term unconditionally remains open; conditional
improvements are known under the Riemann Hypothesis.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Powerful_number)
- [ES35] Erdős, P. and Szekeres, G., *Über die Anzahl der Abelschen Gruppen gegebener Ordnung
  und über ein verwandtes zahlentheoretisches Problem*, Acta Sci. Math. (Szeged) 7 (1935), 95–102.
- [BG58] Bateman, P. T. and Grosswald, E., *On a theorem of Erdős and Szekeres*,
  Illinois J. Math. 2 (1958), 88–98.
-/

open Filter Asymptotics Real

namespace PowerfulNumbersDensity

/-- $Q(x)$ is the number of powerful integers $n$ with $1 \le n \le x$. -/
noncomputable abbrev Q (x : ℝ) : ℕ := {n : ℕ | 0 < n ∧ n.Powerful ∧ (n : ℝ) ≤ x}.ncard

/-- The leading constant $\zeta(3/2)/\zeta(3) = 2.173\ldots$ -/
noncomputable abbrev A : ℝ := (riemannZeta (3 / 2)).re / (riemannZeta 3).re

/-- The second-order constant $\zeta(2/3)/\zeta(2)$, where $\zeta(2/3)$ is given by analytic
continuation. -/
noncomputable abbrev B : ℝ := (riemannZeta (2 / 3)).re / (riemannZeta 2).re

/--
Erdős and Szekeres [ES35] proved that the number of powerful integers up to $x$ satisfies
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + O(x^{1/3}).$$
In particular $Q(x) \sim \frac{\zeta(3/2)}{\zeta(3)} \sqrt{x}$.
-/
@[category research solved, AMS 11]
theorem asymptotic_erdos_szekeres :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 3) := by
  sorry

/--
Bateman and Grosswald [BG58] proved the sharper asymptotic
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} + O(x^{1/6}).$$
-/
@[category research solved, AMS 11]
theorem asymptotic_bateman_grosswald :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6) := by
  sorry

/--
Can the exponent $1/6$ in the error term of the Bateman–Grosswald asymptotic be improved
unconditionally? That is, is there $\delta > 0$ such that
$$Q(x) = \frac{\zeta(3/2)}{\zeta(3)} x^{1/2} + \frac{\zeta(2/3)}{\zeta(2)} x^{1/3} +
O(x^{1/6 - \delta})?$$
Improvements are known under the Riemann Hypothesis.
-/
@[category research open, AMS 11]
theorem error_term_improvement :
    answer(sorry) ↔ ∃ δ > (0 : ℝ),
      (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
        fun x => x ^ ((1 : ℝ) / 6 - δ) := by
  sorry

end PowerfulNumbersDensity
