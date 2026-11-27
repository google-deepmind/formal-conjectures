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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 916

*References:*
- [erdosproblems.com/916](https://www.erdosproblems.com/916)
- [Di60] Dirac, Gabriel Andrew, *In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre
  Unterteilungen*. Math. Nachr. (1960), 61-85.
- [Er67b] Erdős, Paul, *Extremal problems in graph theory*. A Seminar on Graph Theory (1967),
  54-59.
- [Th74] Thomassen, Carsten, *A minimal condition implying a special $K_4$-subdivision in a
  graph*. Arch. Math. (Basel) (1974), 210--215.
-/

@[expose] public section

open SimpleGraph

namespace Erdos916

/--
Does every graph with $n$ vertices and $2n-2$ edges contain a cycle and another vertex adjacent
to three vertices on the cycle?

This would be a stronger form of the result of Dirac [Di60] that every such graph contains a
subgraph homeomorphic to $K_4$. The answer is yes, as proved by Thomassen [Th74].

We assume $n \geq 2$: the graph on one vertex has $2 \cdot 1 - 2 = 0$ edges and no cycle. For
$n = 2, 3$ no graph has $2n-2$ edges, so these cases hold vacuously.
-/
@[category research solved, question, AMS 5]
theorem erdos_916 :
    ∀ n ≥ 2, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → G.edgeSet.ncard = 2 * n - 2 →
        ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ ∃ v ∉ c.support,
          ∃ s : Finset V, s.card = 3 ∧ ∀ w ∈ s, w ∈ c.support ∧ G.Adj v w := by
  sorry

end Erdos916
