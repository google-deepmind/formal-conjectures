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
# Erdős Problem 127

*Reference:* [erdosproblems.com/127](https://www.erdosproblems.com/127)

Let $f(m)$ be the excess of the maximum bipartite subgraph size over the Edwards bound
$m/2 + (\sqrt{8m+1} - 1)/8$. Is $f(m)$ unbounded? Proved by Alon.

[Ed73] Edwards, C.S., _Some extremal properties of bipartite subgraphs_,
Canadian Journal of Mathematics (1973).

[Al96] Alon, N., _Bipartite subgraphs_, Combinatorica 16 (1996), 301–311.
-/

open Real Filter

namespace Erdos127

/--
For a finite simple graph $G$ and a vertex subset $S$, the cut defined by $S$
consists of edges with exactly one endpoint in $S$. We count these as ordered pairs
$(v, w)$ with $v \in S$, $w \notin S$, and $v \sim w$; since the adjacency relation
is symmetric and $S$ and $S^c$ are disjoint, each undirected cut edge is counted exactly
once (from its $S$-side endpoint).
-/
noncomputable def cutSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V =>
    p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2).card

/--
The maximum bipartite subgraph size of $G$: the maximum over all vertex bipartitions
$(S, S^c)$ of the number of edges crossing the cut. This equals the maximum number of
edges in any bipartite subgraph of $G$ (the max-cut).
-/
noncomputable def maxBipartiteSubgraphSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (cutSize G)

/--
The Edwards lower bound: every graph with $m$ edges has a bipartite subgraph of size at
least $m/2 + (\sqrt{8m+1} - 1)/8$. Proved by Edwards [Ed73].
-/
noncomputable def edwardsLB (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/--
$f(m)$ is the maximal value $r$ such that every finite simple graph with $m$ edges has a
bipartite subgraph with at least $\operatorname{edwardsLB}(m) + r$ edges. Equivalently,
$f(m)$ is the infimum over all finite simple graphs $G$ with exactly $m$ edges of the excess
$$\operatorname{maxBipartiteSubgraphSize}(G) - \operatorname{edwardsLB}(m).$$

Edwards [Ed73] proved $f(m) \geq 0$ for all $m$. Note that
$f\left(\binom{n}{2}\right) = 0$, achieved by $K_n$.
-/
noncomputable def f (m : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = m ∧ r = (maxBipartiteSubgraphSize G : ℝ) - edwardsLB m}

/--
Erdős Problem 127 (Erdős–Kohayakawa–Gyárfás; solved by Alon [Al96]):
Let $f(m)$ be maximal such that every graph with $m$ edges contains a bipartite subgraph with
at least $m/2 + (\sqrt{8m+1} - 1)/8 + f(m)$ edges.
There exists an infinite sequence of integers $(m_i)$ with $m_i \to \infty$ such that
$f(m_i) \to \infty$.

Edwards [Ed73] proved $f(m) \geq 0$ for all $m$.
Alon [Al96] proved this in the affirmative: $f(n^2/2) \gg n^{1/2}$.
Alon [Al96] also showed the upper bound $f(m) \ll m^{1/4}$ for all $m$.
-/
@[category research solved, AMS 5]
theorem erdos_127 : answer(True) ↔
    ∃ (seq : ℕ → ℕ), StrictMono seq ∧
      Filter.Tendsto (fun i => f (seq i)) Filter.atTop Filter.atTop := by
  sorry

end Erdos127
