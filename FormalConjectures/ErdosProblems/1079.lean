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
# Erdős Problem 1079

*Reference:* [erdosproblems.com/1079](https://www.erdosproblems.com/1079)
-/

open Filter SimpleGraph
open scoped Topology

namespace Erdos1079

/-- The Turán number $\mathrm{ex}(n;K_r)$: the maximum number of edges in an $n$-vertex $K_r$-free
graph. -/
noncomputable def ex (n r : ℕ) : ℕ :=
  sSup { m | ∃ (G : SimpleGraph (Fin n)),
    ¬ (⊤ : SimpleGraph (Fin r)).IsContained G ∧ G.edgeSet.ncard = m }

/-- Number of edges in the subgraph induced by the neighbourhood of `v`. -/
noncomputable def neighborhoodEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.induce (G.neighborSet v)).edgeSet.ncard

/--
Let $r\geq 4$. If $G$ is a graph on $n$ vertices with at least $\mathrm{ex}(n;K_r)$ edges then must
$G$ contain a vertex with degree $d\gg_r n$ whose neighbourhood contains at least
$\mathrm{ex}(d;K_{r-1})$ edges?
-/
@[category research open, AMS 5]
theorem erdos_1079 :
    answer(sorry) ↔
      ∀ r ≥ 4, ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          ex n r ≤ G.edgeSet.ncard →
            ∃ v : Fin n, C * n ≤ (G.degree v : ℝ) ∧
              ex (G.degree v) (r - 1) ≤ neighborhoodEdges G v := by
  sorry

end Erdos1079
