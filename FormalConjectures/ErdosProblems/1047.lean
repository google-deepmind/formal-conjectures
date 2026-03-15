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
# Erdős Problem 1047

*Reference:* [erdosproblems.com/1047](https://www.erdosproblems.com/1047)

Let $f \in \mathbb{C}[x]$ be a monic polynomial with $m$ distinct roots, and let $c > 0$ be a
constant small enough such that $\{ z : |f(z)| \leq c \}$ has $m$ distinct connected
components. Must all these components be convex?

A question of Grunsky, reported by Erdős, Herzog, and Piranian [EHP58, p.145].

The answer is no, as shown by Pommerenke [Po61], who proved that for
$f(z) = z^k(z-a)$ with $k$ sufficiently large and $a$ close to $(1+1/k)k^{1/(k+1)}$,
the set $\{ z : |f(z)| \leq 1 \}$ has two components and the one containing $0$ is
not convex.

Goodman [Go66] gave further examples, including $(z^2+1)(z-2)^2$ with explicit $c$.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_. J. Analyse
Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J. 8 (1961),
97–115.

[Go66] Goodman, A. W., _On the convexity of the level curves of a polynomial_. Proc. Amer. Math.
Soc. 17 (1966), 358-361.
-/

open Complex Polynomial Set

namespace Erdos1047

/--
Erdős Problem 1047 (Grunsky's question, [EHP58, p.145]):

For a monic polynomial $f \in \mathbb{C}[x]$ with $m$ distinct roots and $c > 0$ such that
the sublevel set $S = \{ z : \|f(z)\| \leq c \}$ has exactly $m$ connected components,
must all these components be convex?

Answered in the negative by Pommerenke [Po61].
-/
@[category research solved, AMS 30 52]
theorem erdos_1047 : answer(False) ↔
    ∀ (f : Polynomial ℂ), f.Monic →
    ∀ (c : ℝ), c > 0 →
      let S := {z : ℂ | ‖Polynomial.eval z f‖ ≤ c}
      Set.ncard (connectedComponentIn S '' S) = f.roots.toFinset.card →
      ∀ x ∈ S, Convex ℝ (connectedComponentIn S x) := by
  sorry

end Erdos1047
