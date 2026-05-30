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
# Erdős Problem 742

*References:*
- [erdosproblems.com/742](https://www.erdosproblems.com/742)
- [Pl75] Plesník, Ján, Critical graphs of given diameter. Acta Fac. Rerum Natur. Univ. Comenian.
  Math. 30 (1975), 71-93.
- [CaHa79] Caccetta, L. and Häggkvist, R., On diameter critical graphs.
  Discrete Math. 28 (1979), 223-229.
- [Fa87] Fan, Genghua, On diameter 2-critical graphs. Discrete Math. 67 (1987), 235-240.
- [Fü92] Füredi, Zoltán, The maximum number of edges in a minimal graph of diameter 2.
  J. Graph Theory 16 (1992), 81-98.
-/

open SimpleGraph

namespace Erdos742

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is diameter-2-critical if it has diameter $2$ and removing any edge
increases the diameter beyond $2$. -/
def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

/--
**Murty-Simon Conjecture**

Let $G$ be a graph on $n$ vertices with diameter $2$ such that deleting any edge increases the
diameter. Is it true that $G$ has at most $\lfloor n^2 / 4 \rfloor$ edges? Equality is conjectured
to hold for the complete balanced bipartite graph $K_{\lceil n/2 \rceil, \lfloor n/2 \rfloor}$.

The conjecture is resolved up to a finite check: Fan [Fa87] verified it for $n \leq 24$ and
$n = 26$, and Füredi [Fü92] proved it for all sufficiently large $n$.
-/
@[category research open, AMS 5]
theorem erdos_742 :
    answer(sorry) ↔ ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], IsDiameter2Critical G →
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry

/--
The complete bipartite graph $K_{a, b}$ has exactly $a \cdot b$ edges. The bound
$\lfloor n^2 / 4 \rfloor$ in the Murty-Simon conjecture is attained by the balanced
case $K_{\lceil n/2 \rceil, \lfloor n/2 \rfloor}$.
-/
@[category test, AMS 5]
theorem complete_bipartite_edge_count (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard = a * b := by
  sorry

namespace variants

/--
Plesník [Pl75] proved the bound $|E(G)| < 3n(n-1)/8$ for any diameter-$2$-critical graph
on $n$ vertices.
-/
@[category research solved, AMS 5]
theorem plesnik_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (G.edgeFinset.card : ℝ) < 3 * (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 8 := by
  sorry

/--
Fan [Fa87] verified the Murty-Simon conjecture for all $n \leq 24$ and for $n = 26$.
-/
@[category research solved, AMS 5]
theorem fan_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≤ 24 ∨ Fintype.card V = 26) (hG : IsDiameter2Critical G) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry

/--
Füredi [Fü92] proved the Murty-Simon conjecture for all sufficiently large $n$, that is, there
exists $n_0$ such that every diameter-$2$-critical graph on $n \geq n_0$ vertices has at most
$\lfloor n^2 / 4 \rfloor$ edges.
-/
@[category research solved, AMS 5]
theorem furedi_bound : ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry

end variants

end Erdos742
