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
  Math. (1975), 71-93.
- [Fa87] Fan, Genghua, On diameter 2-critical graphs. Discrete Math. (1987), 227-234.
- [Fü92] Füredi, Zoltán, The maximum number of edges in a minimal graph of diameter 2.
  J. Graph Theory (1992), 81-98.
-/

open SimpleGraph

namespace Erdos742

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is diameter-2-critical if it has diameter 2 and removing any edge
increases the diameter beyond 2. -/
def IsDiameter2Critical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

/--
**Murty-Simon Conjecture**

A graph is diameter-2-critical if it has diameter 2 and removing any single edge increases
the diameter. The conjecture asserts that such graphs have at most $\lfloor n^2/4 \rfloor$ edges,
with equality achieved by the complete balanced bipartite graph $K_{\lceil n/2 \rceil, \lfloor n/2 \rfloor}$.

Is it true that every diameter-2-critical graph on $n$ vertices has at most $\lfloor n^2/4 \rfloor$ edges?
-/
@[category research open, AMS 5]
theorem erdos_742 :
    answer(sorry) ↔ ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], IsDiameter2Critical G →
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry

/--
The bound $\lfloor n^2/4 \rfloor$ is achieved by the complete balanced bipartite graph
$K_{\lceil n/2 \rceil, \lfloor n/2 \rfloor}$.
This has $\lceil n/2 \rceil \cdot \lfloor n/2 \rfloor = \lfloor n^2/4 \rfloor$ edges.
-/
@[category test, AMS 5]
theorem balanced_bipartite_edge_count (a b : ℕ) :
    (completeBipartiteGraph (Fin a) (Fin b)).edgeSet.ncard = a * b := by
  sorry

namespace variants

/--
Plesník [Pl75] proved the weaker bound of $n^2/4 + n/2$ edges for diameter-2-critical graphs.
-/
@[category research solved, AMS 5]
theorem plesnik_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 + (Fintype.card V : ℝ) / 2 := by
  sorry

/--
Fan [Fa87] proved the bound $\lfloor n^2/4 \rfloor + 1$ for diameter-2-critical graphs.
-/
@[category research solved, AMS 5]
theorem fan_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsDiameter2Critical G) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 + 1 := by
  sorry

/--
Füredi [Fü92] proved that diameter-2-critical graphs have at most
$\lfloor n^2/4 \rfloor + O(n^{3/2})$ edges.
-/
@[category research solved, AMS 5]
theorem furedi_bound : ∃ C > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsDiameter2Critical G →
      (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 + C * (Fintype.card V : ℝ) ^ (3/2) := by
  sorry

end variants

end Erdos742
