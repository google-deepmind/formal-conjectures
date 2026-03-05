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
# Erdős Problem 916

*Reference:* [erdosproblems.com/916](https://www.erdosproblems.com/916)

Does every graph with $n$ vertices and $2n-2$ edges contain a cycle and another
vertex adjacent to three vertices on the cycle?

This would be a stronger form of Dirac's result [Di60] that every such graph
contains a subgraph homeomorphic to $K_4$.

The answer is yes, as proved by Thomassen [Th74].

[Er67b] Erdős, P., _Some recent results on extremal problems in graph theory (Results)_.
Theory of Graphs (Internat. Sympos., Rome, 1966) (1967), 117-123.

[Di60] Dirac, G. A., _In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre
Unterteilungen_. Math. Nachr. 22 (1960), 61-85.

[Th74] Thomassen, C., _Some homeomorphism properties of graphs_. Math. Nachr. 64 (1974),
119-133.
-/

open SimpleGraph Finset

namespace Erdos916

/--
Erdős Problem 916 [Er67b]:

Every simple graph with $n$ vertices and at least $2n-2$ edges contains a cycle $C$
and a vertex $v$ not on $C$ that is adjacent to at least three vertices of $C$.

A cycle of length $m$ ($m \geq 3$) is represented as an injective map
`cycle : Fin m → Fin n` where consecutive vertices (including wrap-around)
are adjacent.
-/
@[category research solved, AMS 5]
theorem erdos_916 : answer(True) ↔
    ∀ (n : ℕ), n ≥ 4 →
    ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    G.edgeFinset.card ≥ 2 * n - 2 →
    ∃ (k : ℕ) (cycle : Fin (k + 3) → Fin n),
      Function.Injective cycle ∧
      (∀ i : Fin (k + 3), G.Adj (cycle i)
        (cycle ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (by omega)⟩)) ∧
      ∃ v : Fin n, v ∉ Set.range cycle ∧
        ∃ (i j l : Fin (k + 3)), i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
          G.Adj v (cycle i) ∧ G.Adj v (cycle j) ∧ G.Adj v (cycle l) := by
  sorry

end Erdos916
