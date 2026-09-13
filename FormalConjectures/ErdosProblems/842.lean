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
# Erdős Problem 842

*Reference:* [erdosproblems.com/842](https://www.erdosproblems.com/842)
-/

open SimpleGraph

namespace Erdos842

/-- `n` vertex-disjoint triangles in `G`. -/
def HasDisjointTriangles {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ t : Fin n → Finset V,
    (∀ i, (t i).card = 3) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      ∀ i, ∀ a ∈ t i, ∀ b ∈ t i, a ≠ b → G.Adj a b

/-- A Hamiltonian cycle: a cyclic permutation of all vertices consisting of edges of `G`. -/
def HasHamiltonianCycle {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ c : Equiv.Perm V, c.IsCycle ∧ ∀ v : V, G.Adj v (c v)

/--
Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles and adding a
Hamiltonian cycle (with all new edges) between these vertices. Does $G$ have chromatic number at
most $3$?
-/
@[category research open, AMS 5]
theorem erdos_842 :
    answer(sorry) ↔
      ∀ n : ℕ, ∀ G : SimpleGraph (Fin (3 * n)),
        HasDisjointTriangles G n → HasHamiltonianCycle G → G.chromaticNumber ≤ 3 := by
  sorry

end Erdos842
