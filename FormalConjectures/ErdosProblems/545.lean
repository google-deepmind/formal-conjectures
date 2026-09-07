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
# Erdős Problem 545

*References:*
- [erdosproblems.com/545](https://www.erdosproblems.com/545)
- [Er75c] Erdős, P., Problems and results on finite and infinite graphs. Recent advances in graph
  theory (Proc. Second Czechoslovak Sympos., Prague, 1974) (1975), 183-192.
-/

namespace Erdos545

/--
The graph formed by connecting a new vertex (`none`) to $t$ of the vertices of $K_n$ (`Fin n`).
-/
def knPlusTEdges (n t : ℕ) : SimpleGraph (Option (Fin n)) where
  Adj u v := match u, v with
    | some x, some y => x ≠ y
    | none, some y => y.val < t
    | some x, none => x.val < t
    | none, none => False
  symm.symm u v := by
    cases u <;> cases v <;> simp [ne_comm]
  loopless.irrefl u := by
    cases u <;> simp

/--
Let $G$ be a graph with $m$ edges and no isolated vertices. Is the Ramsey number $R(G)$ maximised
when $G$ is 'as complete as possible'? That is, if $m=\binom{n}{2}+t$ edges with $0\leq t < n$
then is
$$R(G)\leq R(H),$$
where $H$ is the graph formed by connecting a new vertex to $t$ of the vertices of $K_n$?

A question of Erdős and Graham.

This problem is #10 in Ramsey Theory in the graphs problem collection.
-/
@[category research open, AMS 5]
theorem erdos_545 : answer(sorry) ↔
    ∀ (n t : ℕ), t < n →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, 0 < G.degree v) →
        G.edgeSet.ncard = n.choose 2 + t →
        SimpleGraph.diagonalGraphRamsey G ≤
          SimpleGraph.diagonalGraphRamsey (knPlusTEdges n t) := by
  sorry

-- TODO: Add variants of the problem.

end Erdos545
