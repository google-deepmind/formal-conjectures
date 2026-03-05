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
# Erdős Problem 1046

*Reference:* [erdosproblems.com/1046](https://www.erdosproblems.com/1046)

A problem of Erdős, Herzog, and Piranian [EHP58]. The answer is yes,
proved by Pommerenke [Po59]. Their additional conjecture that the width of
$\{ z : |f(z)| \leq 1 \}$ is always at most $2$ was disproved by Pommerenke.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125-148.

[Po59] Pommerenke, Ch., *Über die Kapazität ebener Kontinuen*,
Math. Ann. 139 (1959), 64-75.
-/

open Complex Polynomial Metric Set

namespace Erdos1046

/--
Erdős Problem 1046 [EHP58, p. 143]:

For any monic polynomial $f \in \mathbb{C}[x]$, if the set
$E = \{ z \in \mathbb{C} : \|f(z)\| < 1 \}$ is connected, then $E$ is contained in a
closed disc of radius $2$.

Proved by Pommerenke [Po59].
-/
@[category research solved, AMS 30]
theorem erdos_1046 : answer(True) ↔
    ∀ (f : Polynomial ℂ), f.Monic →
      IsConnected {z : ℂ | ‖Polynomial.eval z f‖ < 1} →
      ∃ c : ℂ, {z : ℂ | ‖Polynomial.eval z f‖ < 1} ⊆ closedBall c 2 := by
  sorry

end Erdos1046
