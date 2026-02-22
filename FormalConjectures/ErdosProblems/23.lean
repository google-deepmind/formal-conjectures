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
# Erdős Problem 23

*References:*
* [erdosproblems.com/23](https://www.erdosproblems.com/23)
* [OEIS A389646](https://oeis.org/A389646)
-/

open SimpleGraph BigOperators Classical

namespace Erdos23

/--
Every triangle-free graph on $5$ vertices can be made bipartite by removing at most $1$ edge.
This is the $n = 1$ case of Erdős Problem 23.
-/
@[category test, AMS 5]
theorem erdos_23_n1 :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
        H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  sorry

/--
There exists a triangle-free graph on $5$ vertices such that at least $1$ edge must be removed
to make it bipartite. This shows the bound in `erdos_23_n1` is tight.
-/
@[category test, AMS 5]
theorem erdos_23_n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  sorry

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    (hH : H ≤ blowupC5 n) (hBip : H.IsBipartite) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  sorry

/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔
    ∀ (n : ℕ) (V : Type) [Fintype V], Fintype.card V = 5 * n →
      ∀ (G : SimpleGraph V), G.CliqueFree 3 →
        ∃ (H : SimpleGraph V),
          H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ n^2 := by
  sorry

-- TODO: add the remaining variants/statements/comments

end Erdos23
