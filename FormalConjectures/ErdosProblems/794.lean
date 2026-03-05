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
# Erdős Problem 794

Is it true that every 3-uniform hypergraph on $3n$ vertices with at least $n^3 + 1$ edges must
contain either a subgraph on 4 vertices with 3 edges or a subgraph on 5 vertices with 7 edges?
Disproved by Harris.

*Reference:* [erdosproblems.com/794](https://www.erdosproblems.com/794)
-/

namespace Erdos794

/-- A 3-uniform hypergraph $H$ contains a $(k, m)$-subhypergraph if there exist $k$
    vertices spanning at least $m$ edges of $H$. -/
def ContainsSubhypergraph {N : ℕ} (H : Finset (Finset (Fin N))) (k m : ℕ) : Prop :=
  ∃ S : Finset (Fin N), S.card = k ∧ (H.filter (· ⊆ S)).card ≥ m

/--
Erdős Problem 794 (DISPROVED by Harris):

Is it true that every 3-uniform hypergraph on $3n$ vertices with at least $n^3 + 1$
edges must contain either a subgraph on 4 vertices with 3 edges or a subgraph on
5 vertices with 7 edges?

Balogh observed that every 3-uniform hypergraph on 5 vertices with 7
edges contains a sub-hypergraph on 4 vertices with 3 edges, so the second
condition is redundant. Harris provided a counterexample to the remaining
statement: the 3-uniform hypergraph on $\{1, \ldots, 9\}$ with 28 edges, formed by taking
27 edges by choosing one element each from $\{1,2,3\}$, $\{4,5,6\}$, $\{7,8,9\}$, and then
adding the edge $\{1,2,3\}$.
-/
@[category research solved, AMS 5]
theorem erdos_794 : answer(False) ↔ ∀ n : ℕ, ∀ H : Finset (Finset (Fin (3 * n))),
    (∀ e ∈ H, e.card = 3) →
    H.card ≥ n ^ 3 + 1 →
    ContainsSubhypergraph H 4 3 ∨ ContainsSubhypergraph H 5 7 := by
  sorry

end Erdos794
