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
# Erdős Problem 111

*Reference:* [erdosproblems.com/111](https://www.erdosproblems.com/111)

Does there exist a graph with chromatic number $\aleph_1$ such that every $n$-vertex induced
subgraph can be made bipartite by deleting $O(n^{1+\varepsilon})$ edges for every
$\varepsilon > 0$?

[EHS82] Erdős, P., Hajnal, A. and Szemerédi, E., _On almost bipartite large chromatic
graphs_. Annals of Discrete Mathematics, 12 (1982), 117-123.

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
Combinatorica, 1 (1981), 25-42.

[Er87] Erdős, P., _Some problems on finite and infinite graphs_.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467-478.

[Er97d] Erdős, P., _Some of my new and almost new problems and results in
combinatorics and graph theory_ (1997).

[Er97f] Erdős, P., _Some of my new and almost new problems and results in combinatorial
geometry_. (1997)

See also Problem 74.
-/

open SimpleGraph Cardinal

namespace Erdos111

/--
The minimum number of edges that must be deleted from a finite graph $H$ to make
it bipartite (i.e., properly 2-colorable).
-/
noncomputable def minEdgeDeletionsForBipartite {W : Type*} [Fintype W]
    (H : SimpleGraph W) : ℕ :=
  sInf {k : ℕ | ∃ H' : SimpleGraph W,
    H' ≤ H ∧
    Nonempty (H'.Coloring (Fin 2)) ∧
    (H.edgeSet \ H'.edgeSet).ncard = k}

/--
For a graph $G$ and $n \in \mathbb{N}$, $h(G, n)$ is the maximum, over all $n$-vertex
induced subgraphs $H$ of $G$, of the minimum number of edges that must be deleted
from $H$ to make it bipartite.
-/
noncomputable def maxMinEdgeDeletionsForBipartite {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (S : Finset V),
    S.card = n ∧
    k = minEdgeDeletionsForBipartite (G.induce (S : Set V))}

/--
There exists a graph $G$ with chromatic number $\aleph_1$ such that
$h(G, n) \ll n^{1+\varepsilon}$ for every $\varepsilon > 0$.

- For every $G$ with chromatic number $\aleph_1$, $h(G, n) \gg n$, since $G$ must
  contain $\aleph_1$ many vertex-disjoint odd cycles of some fixed length $2r+1$.
- Erdős–Hajnal–Szemerédi [EHS82] proved there exists $G$ with chromatic number
  $\aleph_1$ satisfying $h(G, n) \ll n^{3/2}$.
- Erdős [Er81] conjectured this upper bound can be improved: there should exist $G$
  with chromatic number $\aleph_1$ such that $h(G, n) \ll n^{1+\varepsilon}$ for
  every $\varepsilon > 0$.
-/
@[category research open, AMS 5]
theorem erdos_111 : answer(sorry) ↔
    ∃ (V : Type*) (G : SimpleGraph V),
      G.chromaticCardinal = aleph 1 ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ n : ℕ, (maxMinEdgeDeletionsForBipartite G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) := by
  sorry

end Erdos111
