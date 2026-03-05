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
# Erdős Problem 915

*Reference:* [erdosproblems.com/915](https://www.erdosproblems.com/915)

Let $G$ be a graph with $1 + n(m-1)$ vertices and $1 + n\binom{m}{2}$ edges.
Must $G$ contain two vertices which are connected by $m$ disjoint paths?

A conjecture of Bollobás and Erdős [BoEr62]. It is unclear whether "disjoint"
means edge-disjoint or (internally) vertex-disjoint. The construction of $n$
copies of $K_m$ sharing a single vertex is valid for either interpretation.

The vertex-disjoint version was disproved by Leonard [Le73] for $m = 5$ and by
Mader [Ma73] for all $m \geq 6$. The edge-disjoint version was confirmed (and
strengthened) by Mader [Ma73].

[BoEr62] Bollobás, B. and Erdős, P., 1962.

[Le73] Leonard, 1973.

[Ma73] Mader, W., 1973.
-/

open SimpleGraph Finset

namespace Erdos915

/-- Two vertices $u$, $v$ in a simple graph $G$ are connected by $m$ internally
vertex-disjoint paths if there exist $m$ paths from $u$ to $v$ such that
no internal vertex of one path appears as an internal vertex of another. -/
def HasInternallyDisjointPaths {V : Type*} (G : SimpleGraph V)
    (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → G.Walk u v),
    (∀ i, (paths i).IsPath) ∧
    (∀ i j, i ≠ j → ∀ w : V, w ≠ u → w ≠ v →
      w ∈ (paths i).support → w ∉ (paths j).support)

/--
Erdős Problem 915 (Bollobás–Erdős conjecture [BoEr62]):

Let $G$ be a graph with $1 + n(m-1)$ vertices and at least $1 + n\binom{m}{2}$ edges.
Must $G$ contain two vertices connected by $m$ internally vertex-disjoint paths?

This was disproved by Leonard [Le73] for $m = 5$ and by Mader [Ma73] for all
$m \geq 6$. The edge-disjoint analogue was confirmed by Mader.
-/
@[category research solved, AMS 5]
theorem erdos_915 : answer(False) ↔
    ∀ (n m : ℕ), m ≥ 2 →
    ∀ (G : SimpleGraph (Fin (1 + n * (m - 1)))) [DecidableRel G.Adj],
    G.edgeFinset.card ≥ 1 + n * m.choose 2 →
    ∃ u v : Fin (1 + n * (m - 1)), u ≠ v ∧
      HasInternallyDisjointPaths G u v m := by
  sorry

end Erdos915
