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
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions

/-!
# Erdős Problem 915

*Reference:* [erdosproblems.com/915](https://www.erdosproblems.com/915)

Let $G$ be a graph with $1 + n(m-1)$ vertices and $1 + n\binom{m}{2}$ edges.
Must $G$ contain two vertices which are connected by $m$ disjoint paths?

A conjecture of Bollobás and Erdős [BoEr62]. It is unclear whether "disjoint"
means edge-disjoint or (internally) vertex-disjoint. The construction of $n$
copies of $K_m$ sharing a single vertex is valid for either interpretation.

The vertex-disjoint version was disproved by Leonard [Le73] for $m = 5$ and by
Mader [Ma73] for all $m \geq 6$. The cases $m = 2, 3, 4$ were confirmed by
Bártfai [Ba60] and Bollobás [Bo66]. The edge-disjoint version was confirmed
(and strengthened) by Mader [Ma73], who showed
$\ell_m(n) = \lfloor m(n-1)/2 + 1 \rfloor$ for all $m \geq 2$.

[Ba60] Bártfai, P., _Solution of a problem posed by P. Erdős_. Mat. Lapok
(1960), 175–176.

[Bo66] Bollobás, B., _On graphs with at most three independent paths
connecting any two vertices_. Studia Sci. Math. Hungar. (1966), 137–140.

[BoEr62] Bollobás, B. and Erdős, P., _Extremal problems in graph theory_.
Mat. Lapok (1962), 143–152.

[Le72] Leonard, J. L., _On graphs with at most four line-disjoint paths
connecting any two vertices_. J. Combinatorial Theory Ser. B (1972), 242–250.

[Le73] Leonard, J. L., _On a conjecture of Bollobás and Erdős_. Period. Math.
Hungar. (1973), 281–284.

[Le73b] Leonard, J. L., _Graphs with 6-ways_. Canadian J. Math. (1973),
687–692.

[Ma73] Mader, W., _Ein Extremalproblem des Zusammenhangs von Graphen_. Math.
Z. (1973), 223–231.

[SoTh74] Sørensen, B. A. and Thomassen, C., _On k-rails in graphs_. J.
Combinatorial Theory Ser. B (1974), 143–159.
-/

open SimpleGraph Finset

namespace Erdos915

/-- Two vertices $u$, $v$ in a simple graph $G$ are connected by $m$ internally
vertex-disjoint paths if there exist $m$ paths from $u$ to $v$ such that
no internal vertex of one path appears as an internal vertex of another. -/
def HasInternallyDisjointPaths {V : Type*} (G : SimpleGraph V)
    (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → G.Walk u v),
    (∀ i, (paths i).IsPath) ∧
    (∀ i j, i ≠ j → InternallyDisjoint (paths i) (paths j))

/-- Two vertices $u$, $v$ in a simple graph $G$ are connected by $m$
edge-disjoint paths if there exist $m$ walks from $u$ to $v$ such that
no edge appears in more than one walk. -/
def HasEdgeDisjointPaths {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → G.Walk u v),
    (∀ i, (paths i).IsPath) ∧
    (∀ i j, i ≠ j → Disjoint (paths i).edges.toFinset (paths j).edges.toFinset)

/--
Erdős Problem 915 (Bollobás–Erdős conjecture [BoEr62]):

Let $G$ be a graph with $1 + n(m-1)$ vertices and at least $1 + n\binom{m}{2}$ edges.
Must $G$ contain two vertices connected by $m$ internally vertex-disjoint paths?

This was disproved by Leonard [Le73] for $m = 5$ and by Mader [Ma73] for all
$m \geq 6$. The edge-disjoint analogue was confirmed by Mader.
-/
@[category research solved, AMS 5]
theorem erdos_915 : answer(False) ↔
    ∀ (n m : ℕ), m ≥ 2 →
    ∀ (G : SimpleGraph (Fin (1 + n * (m - 1)))) [DecidableRel G.Adj],
    G.edgeFinset.card ≥ 1 + n * m.choose 2 →
    ∃ u v : Fin (1 + n * (m - 1)), u ≠ v ∧
      HasInternallyDisjointPaths G u v m := by
  sorry

/--
Edge-disjoint version of Erdős Problem 915:

Mader [Ma73] confirmed that for all $m \geq 2$, if a graph $G$ has
$1 + n(m-1)$ vertices and at least $\lfloor m(n-1)/2 + 1 \rfloor$ edges,
then $G$ contains two vertices connected by $m$ edge-disjoint paths.
-/
@[category research solved, AMS 5]
theorem erdos_915_edge_disjoint : answer(True) ↔
    ∀ (n m : ℕ), m ≥ 2 →
    ∀ (G : SimpleGraph (Fin (1 + n * (m - 1)))) [DecidableRel G.Adj],
    G.edgeFinset.card ≥ (m * (n - 1)) / 2 + 1 →
    ∃ u v : Fin (1 + n * (m - 1)), u ≠ v ∧
      HasEdgeDisjointPaths G u v m := by
  sorry

end Erdos915
