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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Edge Ramsey properties
-/

@[expose] public section

namespace SimpleGraph

/-- A graph `G` is *edge-Ramsey for `K_l` with `k` colours* (in arrow notation,
$G \to (K_l)^e_k$) if every $k$-colouring of the edges of `G` contains a monochromatic copy of
$K_l$. -/
def IsEdgeRamseyForClique {V : Type*} (G : SimpleGraph V) (k l : ℕ) : Prop :=
  ∀ c : G.edgeSet → Fin k, ∃ i : Fin k, ∃ S : Finset V, S.card = l ∧
    ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = i

end SimpleGraph
