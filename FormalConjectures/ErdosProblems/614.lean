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
# Erdős Problem 614

*References:*
- [erdosproblems.com/614](https://www.erdosproblems.com/614)
- [A problem on sparse induced subgraphs](https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/SparseInducedSubgraphs.html)
- [FRS97] Faudree, R. J., Rousseau, C. C. and Schelp, R. H., *Problems in graph theory from Memphis*.
  The Mathematics of Paul Erdős, II, 7–26.
-/

@[expose] public section

namespace Erdos614

def erdos_614.answer : ℕ → ℕ → ℕ := sorry

open scoped Classical in
/--
Let $f(n,k)$ be minimal such that there is a graph with $n$ vertices and $f(n,k)$ edges
where every set of $k+2$ vertices induces a subgraph with maximum degree at least $k$.
Determine $f(n,k)$.
-/
@[category research open, question value, AMS 5]
theorem erdos_614 :
    let f : ℕ → ℕ → ℕ := erdos_614.answer
    ∀ n k, IsLeast {m : ℕ | ∃ G : SimpleGraph (Fin n), G.edgeFinset.card = m ∧
      ∀ s : Finset (Fin n), s.card = k + 2 →
        ∃ v : s, k ≤ (G.induce (s : Set (Fin n))).degree v} (f n k) := by
  sorry

end Erdos614
