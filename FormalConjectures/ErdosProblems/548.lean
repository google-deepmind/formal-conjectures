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
# Erdős Problem 548

*Reference:* [erdosproblems.com/548](https://www.erdosproblems.com/548)

This is the Erdős–Sós conjecture.

[Er64c] Erdős, P., *Extremal problems in graph theory*, 1964.

[Er74c] Erdős, P., *Problems and results on graph theory and combinatorics*, 1974.

[Er93] Erdős, P., 1993.
-/

open SimpleGraph

namespace Erdos548

/-- A graph $H$ contains a copy of graph $G$ (as a subgraph) if there is an injective
function from $V(G)$ to $V(H)$ that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/--
Erdős Problem 548 [Er64c][Er74c, p.78][Er93, p.345]:

Let $n \geq k + 1$. Every graph on $n$ vertices with at least
$\frac{k-1}{2} \cdot n + 1$ edges contains every tree on $k + 1$ vertices.

The edge condition is expressed as $2 \cdot |E(G)| \geq (k-1) \cdot n + 2$ to avoid
division in the naturals.
-/
@[category research open, AMS 5]
theorem erdos_548 (k n : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n))
    (hE : 2 * G.edgeSet.ncard ≥ (k - 1) * n + 2)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) :
    ContainsSubgraphCopy T G := by
  sorry

end Erdos548
