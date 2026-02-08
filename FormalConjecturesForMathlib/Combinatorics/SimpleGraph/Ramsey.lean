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

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Nat.Lattice

/-!
# Graph Ramsey Number

This file defines the classical Ramsey number `R(G, H)` for simple graphs.

## Definition

The Ramsey number `R(G, H)` is the smallest natural number `N` such that any 2-coloring
of the edges of the complete graph `K_N` contains a copy of `G` in the first color
or a copy of `H` in the second color.

Equivalently, for any graph `R` on `N` vertices, either `G` is a subgraph of `R`
or `H` is a subgraph of the complement `Rᶜ`.
-/

namespace SimpleGraph

/--
The Ramsey number `R(G, H)` is the smallest natural number `N` such that for any graph `R`
on `N` vertices, either `G` is contained in `R` or `H` is contained in `Rᶜ`.
-/
noncomputable def Ramsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf { N | ∀ (R : SimpleGraph (Fin N)), G.IsContained R ∨ H.IsContained Rᶜ }

end SimpleGraph
