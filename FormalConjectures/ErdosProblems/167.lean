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
# Erdős Problem 167

*References:*
- [erdosproblems.com/167](https://www.erdosproblems.com/167)
- [Er88] Erdős, P., *Problems and results in combinatorial analysis and graph theory*.
  Discrete Math. (1988), 81-92.
- [Ha99] Haxell, P. E., *Packing and covering triangles in graphs*. Discrete Math. (1999),
  251-254.
- [KaPa22] Kahn, J. and Park, J., *Tuza's conjecture for random graphs*. Random Structures
  Algorithms (2022).
-/

@[expose] public section

namespace Erdos167

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/--
If $G$ is a graph with at most $k$ edge disjoint triangles then can $G$ be made triangle-free
after removing at most $2k$ edges?

A problem of Tuza.
-/
@[category research open, AMS 5]
theorem erdos_167 : answer(sorry) ↔
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ),
      (∀ T, IsTrianglePacking G T → T.card ≤ k) → CanBeMadeTriangleFree G (2 * k) := by
  sorry

/--
It is trivial that $G$ can be made triangle-free after removing at most $3k$ edges: delete all
edges of a maximal family of edge-disjoint triangles.
-/
@[category textbook, AMS 5]
theorem erdos_167.variants.three_mul [Fintype V] (G : SimpleGraph V) (k : ℕ)
    (hk : ∀ T, IsTrianglePacking G T → T.card ≤ k) : CanBeMadeTriangleFree G (3 * k) := by
  sorry

/--
The example of $K_4$ shows that $2k$ would be best possible: $K_4$ has at most one edge
disjoint triangle, but cannot be made triangle-free by removing one edge.
-/
@[category textbook, AMS 5]
theorem erdos_167.variants.K4 :
    (∀ T, IsTrianglePacking (⊤ : SimpleGraph (Fin 4)) T → T.card ≤ 1) ∧
      ¬ CanBeMadeTriangleFree (⊤ : SimpleGraph (Fin 4)) 1 := by
  sorry

end Erdos167
