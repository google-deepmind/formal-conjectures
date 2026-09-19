/-
Copyright 2025 The Formal Conjectures Authors.

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
# Erdős Problem 842

*References:*
- [erdosproblems.com/842](https://www.erdosproblems.com/842)
- [Er92b] Erdős, Paul, _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231-240.
- [FlSt92] Fleischner, Herbert and Stiebitz, Michael, _A solution to a colouring problem of
  P. Erdős_. Discrete Math. (1992), 39--48.
-/

@[expose] public section

open SimpleGraph

namespace Erdos842

/-- `G` is a graph on `3n` vertices formed by taking `n` vertex-disjoint triangles `T` and adding
a Hamiltonian cycle `C` (with all new edges): `G = T ⊔ C` with `T` and `C` edge-disjoint. -/
def IsTrianglesPlusHamiltonianCycle {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ T C : SimpleGraph V, G = T ⊔ C ∧ Disjoint T C ∧
    (∃ e : V ≃ Fin n × Fin 3, ∀ u v, T.Adj u v ↔ u ≠ v ∧ (e u).1 = (e v).1) ∧
    ∃ e : Fin (3 * n) ≃ V, C = (cycleGraph (3 * n)).map e.toEmbedding

/--
Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles and adding a
Hamiltonian cycle (with all new edges) between these vertices. Does $G$ have chromatic number at
most $3$?

The answer is yes, proved by Fleischner and Stiebitz [FlSt92].
-/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos842.lean#L46"]
theorem erdos_842 : answer(True) ↔
    ∀ (V : Type) (G : SimpleGraph V) (n : ℕ), IsTrianglesPlusHamiltonianCycle G n →
      G.chromaticNumber ≤ 3 := by
  sorry

end Erdos842
