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

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Size Ramsey Number

This file defines the size Ramsey number for simple graphs.

## Definition

The size Ramsey number `r̂(G, H)` is the minimum number of edges in a graph `F`
such that any 2-coloring of `F`'s edges contains a copy of `G` in one color or `H` in the other.
-/

namespace SimpleGraph

/--
The size Ramsey number `r̂(G, H)` is the minimum number of edges in a graph `F`
such that any 2-coloring of `F`'s edges contains a copy of `G` in one color or `H` in the other.

A 2-coloring is represented by a subgraph `R ≤ F` (the "red" edges); the "blue" edges are `F \ R`.
-/
noncomputable def sizeRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { m | ∃ (n : ℕ) (F : SimpleGraph (Fin n)),
    F.edgeSet.ncard = m ∧
    ∀ (R : SimpleGraph (Fin n)), R ≤ F →
      G.IsContained R ∨ H.IsContained (F \ R) }

/--
A graph `G` is **Ramsey size linear** if there exists a constant `c > 0` such that
for all graphs `H` with `m` edges and no isolated vertices, `r̂(G, H) ≤ c · m`.
-/
def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (sizeRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

end SimpleGraph
