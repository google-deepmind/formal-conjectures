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
# Erdős Problem 621

*References:*
- [erdosproblems.com/621](https://www.erdosproblems.com/621)
- [EGT96] Erdős, Paul and Gallai, Tibor and Tuza, Zsolt, *Covering and independence in triangle
  structures*. Discrete Math. (1996), 89-101.
- [NoSu16] S. Norin and Y.-R. Sun, *Triangle-free independent sets vs. cuts*. arXiv:1602.04370
  (2016).
-/

open SimpleGraph Classical

namespace Erdos621

/--
Let $G$ be a graph on $n$ vertices, $\alpha_1(G)$ be the maximum number of edges that contain
at most one edge from every triangle, and $\tau_1(G)$ be the minimum number of edges that
contain at least one edge from every triangle.

Is it true that\[\alpha_1(G)+\tau_1(G) \leq \frac{n^2}{4}?\]

A problem of Erdős, Gallai, and Tuza [EGT96], who observe that this is probably quite difficult
since there are different examples where equality hold: the complete graph, the complete
bipartite graph, and the graph obtained from $K_{m,m}$ by adding one vertex joined to every
other.

This is true, and was proved by Norin and Sun [NoSu16], who in fact proved
that\[\alpha_1(G)+\tau_B(G) \leq \frac{n^2}{4},\]where $\tau_B(G)$ is the minimum number of
edges that need to be removed to make the graph bipartite.

Here $\alpha_1(G)$ and $\tau_1(G)$ are taken over subsets of the edge set of $G$, and the
inequality is stated multiplied through by $4$ so that it lives in the natural numbers.
-/
@[category research solved, AMS 5]
theorem erdos_621 : answer(True) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (a t : ℕ),
      IsGreatest {k : ℕ | ∃ A ⊆ G.edgeFinset, A.card = k ∧
        ∀ x y z : Fin n, G.Adj x y → G.Adj y z → G.Adj x z →
          (({s(x, y), s(y, z), s(x, z)} : Finset (Sym2 (Fin n))) ∩ A).card ≤ 1} a →
      IsLeast {k : ℕ | ∃ T ⊆ G.edgeFinset, T.card = k ∧
        ∀ x y z : Fin n, G.Adj x y → G.Adj y z → G.Adj x z →
          (T ∩ ({s(x, y), s(y, z), s(x, z)} : Finset (Sym2 (Fin n)))).Nonempty} t →
      4 * (a + t) ≤ n ^ 2 := by
  sorry

end Erdos621
