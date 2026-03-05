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

*Reference:* [erdosproblems.com/742](https://www.erdosproblems.com/742)

A conjecture of Murty and Plesnik (see [CaHa79]), also attributed to Ore.
The complete bipartite graph shows that this would be best possible.
This is true (for sufficiently large $n$) and was proved by Füredi [Fu92].
-/

open Classical SimpleGraph

namespace Erdos742

/--
**Erdős Problem 742** [Er81]:

Let $G$ be a graph on $n$ vertices with diameter $2$, such that deleting any edge
increases the diameter (either by disconnecting the graph or increasing it
beyond $2$). Then $G$ has at most $n^2/4$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_742 : answer(True) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected →
      G.diam = 2 →
      (∀ v w : Fin n, G.Adj v w →
        ¬(G.deleteEdges {Sym2.mk (v, w)}).Connected ∨
        2 < (G.deleteEdges {Sym2.mk (v, w)}).diam) →
      G.edgeFinset.card ≤ n ^ 2 / 4 := by
  sorry

end Erdos742
