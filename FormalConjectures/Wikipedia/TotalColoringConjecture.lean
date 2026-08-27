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
# The total colouring conjecture (Behzad 1965, Vizing 1968)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Total_coloring)
* [Be65] Behzad, M. (1965). *Graphs and their chromatic numbers.* Ph.D. thesis, Michigan State
  University.
* [Vi68] Vizing, V. G. (1968). "Some unsolved problems in graph theory."
  *Uspekhi Mat. Nauk* 23, pp. 117--134.
* [Ko96] Kostochka, A. V. (1996). "The total chromatic number of any multigraph with maximum
  degree five is at most seven." *Discrete Math.* 162, pp. 199--214.
* [MR98] Molloy, M. and Reed, B. (1998). "A bound on the total chromatic number."
  *Combinatorica* 18, pp. 241--280.
* [Yap96] Yap, H. P. (1996). *Total colourings of graphs.* Lecture Notes in Mathematics 1623,
  Springer.
-/

open SimpleGraph

namespace TotalColoringConjecture

/--
**The total colouring conjecture (Behzad 1965, Vizing 1968).**

Every finite simple graph $G$ has a total colouring with at most $\Delta(G) + 2$ colours, i.e.
$\chi''(G) \le \Delta(G) + 2$, where $\Delta(G)$ is the maximum degree.
-/
@[category research open, AMS 5]
theorem total_coloring_conjecture : answer(sorry) ↔
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.totalChromaticNumber ≤ G.maxDegree + 2 := by
  sorry

/--
**Maximum degree at most `5` (Rosenfeld and Vijayaditya for $\Delta \le 3$; Kostochka for
$\Delta = 4, 5$).**

The conjecture holds for every graph of maximum degree at most $5$.

*References:* [Ko96], [Yap96].
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.maxDegree_le_five
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hΔ : G.maxDegree ≤ 5) :
    G.totalChromaticNumber ≤ G.maxDegree + 2 := by
  sorry

/--
**Complete graphs.**

The total chromatic number of $K_n$ is $n$ for odd $n$ and $n + 1$ for even $n$ (see [Yap96]),
so in particular the conjecture holds for complete graphs.
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.complete_graph (n : ℕ) :
    (completeGraph (Fin n)).totalChromaticNumber ≤ (completeGraph (Fin n)).maxDegree + 2 := by
  sorry

/--
**Molloy–Reed (1998): $\chi''(G) \le \Delta(G) + C$ for an absolute constant $C$.**

There is a constant $C$ (Molloy and Reed obtain $C = 10^{26}$) such that every graph satisfies
$\chi''(G) \le \Delta(G) + C$.

*Reference:* [MR98].
-/
@[category research solved, AMS 5]
theorem total_coloring_conjecture.variants.molloy_reed :
    ∃ C : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.totalChromaticNumber ≤ G.maxDegree + C := by
  sorry

/--
**Sanity check: the trivial bound.** Colouring all vertices and edges with distinct colours
shows $\chi''(G) \le |V| + |E|$; this is `SimpleGraph.totalChromaticNumber_le_card_add_card`.
-/
@[category test, AMS 5]
theorem totalChromaticNumber_le_card_add_card
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.totalChromaticNumber ≤ Fintype.card V + Fintype.card G.edgeSet :=
  G.totalChromaticNumber_le_card_add_card

end TotalColoringConjecture
