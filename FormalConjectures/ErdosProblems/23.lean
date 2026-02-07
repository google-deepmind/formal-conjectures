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
-/

open SimpleGraph BigOperators

namespace Erdos23

/--
The blow-up of the 5-cycle $C_5$: replace each vertex of $C_5$ with an independent set of $n$
vertices, and connect two vertices iff their corresponding vertices in $C_5$ are adjacent.
The vertex set is $\mathbb{Z}/5\mathbb{Z} \times \{0, \ldots, n-1\}$, where $(i, a)$ and $(j, b)$
are adjacent iff $j = i + 1$ or $i = j + 1$ in $\mathbb{Z}/5\mathbb{Z}$.
-/
def blowupC5 (n : ℕ) : SimpleGraph (ZMod 5 × Fin n) :=
  SimpleGraph.fromRel fun (i, _) (j, _) => i + 1 = j ∨ j + 1 = i

instance (n : ℕ) : DecidableRel (blowupC5 n).Adj :=
  fun _ _ => instDecidableAnd

/--
The blow-up of $C_5$ shows that the bound $n^2$ in Erdős Problem 23 is tight:
any bipartite subgraph must omit at least $n^2$ edges.
-/
@[category test, AMS 5]
theorem blowupC5_tight (n : ℕ) (_hn : 0 < n) (H : SimpleGraph (ZMod 5 × Fin n))
    [DecidableRel H.Adj] (hH : H ≤ blowupC5 n) (hBip : H.Colorable 2) :
    n ^ 2 ≤ ((blowupC5 n).edgeFinset \ H.edgeFinset).card := by
  sorry

def Erdos23Prop (n : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = 5 * n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      G.CliqueFree 3 →
      ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H ≤ G ∧
        H.Colorable 2 ∧
        (G.edgeFinset \ H.edgeFinset).card ≤ n^2

/--
Can every triangle-free graph on $5n$ vertices be made bipartite by deleting at most $n^2$ edges?
-/
@[category research open, AMS 5]
theorem erdos_23 : answer(sorry) ↔ ∀ n, Erdos23Prop n := by
  sorry

end Erdos23
