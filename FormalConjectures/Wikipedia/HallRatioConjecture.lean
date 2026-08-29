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

import FormalConjecturesUtil

/-!
# The Hall ratio conjecture (Harris 2019) — disproved

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Fractional_coloring)
* [Ha19] Harris, D. G. (2019). "Some results on chromatic number as a function of triangle
  count." *SIAM J. Discrete Math.* 33, pp. 546--563.
* [DOW20] Dvořák, Z., Ossona de Mendez, P. and Wu, H. (2020). "1-subdivisions, the fractional
  chromatic number and the Hall ratio." *Combinatorica* 40, pp. 759--774.
  [arXiv:1812.07327](https://arxiv.org/abs/1812.07327)
* [BLMNPV22] Blumenthal, A., Lidický, B., Martin, R. R., Norin, S., Pfender, F. and Volec, J.
  (2022). "Counterexamples to a conjecture of Harris on Hall ratio." *SIAM J. Discrete Math.*
  36, pp. 1678--1686. [arXiv:1811.11116](https://arxiv.org/abs/1811.11116)
* [SU97] Scheinerman, E. R. and Ullman, D. H. (1997). *Fractional Graph Theory.* Wiley.
-/

open SimpleGraph

namespace HallRatioConjecture

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **Hall ratio** `ρ(G)`: the maximum of `|V(H)| / α(H)` over nonempty induced subgraphs
`H` of `G` (`α` the independence number). -/
noncomputable def hallRatio (G : SimpleGraph V) : ℝ :=
  sSup {r | ∃ S : Finset V, S.Nonempty ∧
    r = (S.card : ℝ) / ((G.induce (S : Set V)).indepNum : ℝ)}

/--
**The Hall ratio conjecture (Harris 2019) — disproved.**

Harris conjectured that the fractional chromatic number is bounded by a constant multiple of the
Hall ratio: there is a constant $C$ with $\chi_f(G) \le C\,\rho(G)$ for every graph $G$. This
is **false**: Dvořák, Ossona de Mendez and Wu [DOW20] and, independently, Blumenthal, Lidický,
Martin, Norin, Pfender and Volec [BLMNPV22] constructed graphs with $\chi_f / \rho$
arbitrarily large.
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture : answer(False) ↔
    ∃ C : ℝ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.fractionalChromaticNumber ≤ C * hallRatio G := by
  sorry

/--
**The Hall ratio is a lower bound for the fractional chromatic number.**

For every graph, $\rho(G) \le \chi_f(G)$ (see [SU97]); the conjecture asked for an inequality in
the other direction up to a constant.
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    hallRatio G ≤ G.fractionalChromaticNumber := by
  sorry

/--
**Unbounded ratio (Dvořák–Ossona de Mendez–Wu 2020; Blumenthal et al. 2022).**

For every $C$ there is a graph with $\chi_f(G) > C\,\rho(G)$.

*References:* [DOW20], [BLMNPV22].
-/
@[category research solved, AMS 5]
theorem hall_ratio_conjecture.variants.unbounded (C : ℝ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      C * hallRatio G < G.fractionalChromaticNumber := by
  sorry

/--
**The fractional chromatic number is at most the number of vertices.**

This is the trivial bound `SimpleGraph.fractionalChromaticNumber_le_card`, recorded here as a
sanity check on the definition.
-/
@[category test, AMS 5]
theorem fractionalChromaticNumber_le_card (G : SimpleGraph V) :
    G.fractionalChromaticNumber ≤ Fintype.card V :=
  G.fractionalChromaticNumber_le_card

end HallRatioConjecture
