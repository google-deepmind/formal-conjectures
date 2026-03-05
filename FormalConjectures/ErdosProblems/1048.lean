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
# Erdős Problem 1048

Erdős, Herzog, and Piranian asked whether, for a monic polynomial over ℂ with all roots in a
disk of radius r < 2, the sublevel set {z : |f(z)| < 1} must contain a connected component of
diameter greater than 2 − r. Pommerenke disproved this for r > 1.

*Reference:* [erdosproblems.com/1048](https://www.erdosproblems.com/1048)

[EHP58] Erdős, P., Herzog, F. and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., *On metric properties of complex polynomials*,
Michigan Math. J. 8 (1961), 97-115.
-/

open Polynomial Metric

namespace Erdos1048

/--
Erdős Problem 1048 [EHP58, p.142] (disproved by Pommerenke [Po61]):

If $f \in \mathbb{C}[x]$ is a monic polynomial with all roots satisfying $|z| \leq r$ for some
$r < 2$, must $\{ z : |f(z)| < 1 \}$ have a connected component with diameter $> 2 - r$?

Pommerenke [Po61] proved the answer is no for $r > 1$, showing that if
$f(z) = z^n - r^n$ then $\{ z : |f(z)| \leq 1 \}$ has $n$ connected components, all with
diameter $\to 0$ as $n \to \infty$.

For $0 < r \leq 1$, the answer is yes (also Pommerenke [Po61]).
-/
@[category research solved, AMS 30]
theorem erdos_1048 : answer(False) ↔
    ∀ (r : ℝ), r < 2 → ∀ (f : Polynomial ℂ), f.Monic →
      (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      let S := {z : ℂ | ‖Polynomial.eval z f‖ < 1}
      ∃ z ∈ S, 2 - r < diam (connectedComponentIn S z) := by
  sorry

end Erdos1048
