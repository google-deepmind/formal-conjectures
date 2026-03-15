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
# Erdős Problem 581

Determine the maximum number of edges in a bipartite subgraph that every
triangle-free graph with $m$ edges must contain.

*Reference:* [erdosproblems.com/581](https://www.erdosproblems.com/581)

[CEG79] Chung, F. R. K., Erdős, P., and Graham, R. L., 1979.

[Al96] Alon, N., *Bipartite subgraphs*. Combinatorica 16 (1996), 301–311.
-/

open SimpleGraph

namespace Erdos581

/--
The maximum number of edges in a bipartite spanning subgraph of a graph $G$ on
a finite vertex type. A spanning subgraph $H \leq G$ is bipartite iff it admits a
proper 2-coloring (i.e., is bipartite). We use `Set.ncard` to count edges, avoiding the need for
decidability instances.
-/
noncomputable def maxBipartiteEdges {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ H : SimpleGraph V, H ≤ G ∧
    H.IsBipartite ∧
    H.edgeSet.ncard = k}

/--
$f(m)$ is the largest $k$ such that every triangle-free graph on $m$ edges must
contain a bipartite subgraph with at least $k$ edges. Equivalently, $f(m)$ is
the infimum of `maxBipartiteEdges G` over all finite triangle-free graphs $G$
with exactly $m$ edges. We quantify over graphs on `Fin n` for all $n$, which
suffices since every finite graph is isomorphic to one on `Fin n`.
-/
noncomputable def f (m : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 ∧
    G.edgeSet.ncard = m ∧
    maxBipartiteEdges G = k}

/--
Erdős Problem 581 [CEG79]:

Let $f(m)$ be the maximal $k$ such that a triangle-free graph on $m$ edges must
contain a bipartite graph with $k$ edges. Determine $f(m)$.

Resolved by Alon [Al96], who showed that there exist constants $c_1, c_2 > 0$
such that $m/2 + c_1 \cdot m^{4/5} \leq f(m) \leq m/2 + c_2 \cdot m^{4/5}$.
-/
@[category research solved, AMS 5]
theorem erdos_581 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ m : ℕ, 0 < m →
        (m : ℝ) / 2 + c₁ * (m : ℝ) ^ ((4 : ℝ) / 5) ≤ (f m : ℝ) ∧
        (f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ ((4 : ℝ) / 5) := by
  sorry

end Erdos581
