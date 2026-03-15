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
      let E := {z : ℂ | ‖Polynomial.eval z f‖ < 1}
      IsConnected E →
      ∃ c : ℂ, E ⊆ closedBall c 2 := by
  sorry

/--
Strengthening of Erdős Problem 1046: Pommerenke [Po59] proved that the center of the
containing disc of radius $2$ can be taken to be the centroid (arithmetic mean) of the
roots of $f$, i.e., $\frac{z_1 + \cdots + z_n}{n}$.
-/
@[category research solved, AMS 30]
theorem erdos_1046_centroid :
    ∀ (f : Polynomial ℂ), f.Monic →
      let E := {z : ℂ | ‖Polynomial.eval z f‖ < 1}
      IsConnected E →
      E ⊆ closedBall (f.roots.sum / (f.natDegree : ℂ)) 2 := by
  sorry

/--
Width conjecture from [EHP58]: Erdős, Herzog, and Piranian conjectured that if
$\{ z : |f(z)| \leq 1 \}$ is connected, then its width is at most $2$. This was disproved
by Pommerenke [Po59], who gave an example with width $> \sqrt{3} \cdot 2^{1/3} \approx 2.18$.

The width of a planar set $S$ is the infimum over unit directions $u$ of
$\sup_{z_1, z_2 \in S} |\operatorname{Re}((z_1 - z_2) \cdot \bar{u})|$.
-/
@[category research solved, AMS 30]
theorem erdos_1046_width : answer(False) ↔
    ∀ (f : Polynomial ℂ), f.Monic →
      let E := {z : ℂ | ‖Polynomial.eval z f‖ ≤ 1}
      IsConnected E →
      ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z₁ ∈ E, ∀ z₂ ∈ E,
        |((z₁ - z₂) * starRingEnd ℂ u).re| ≤ 2 := by
  sorry

end Erdos1046
