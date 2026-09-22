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

public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

/-!
# Decidable adjacency in box products

Adjacency in `G □ H` is decidable when adjacency in `G` and `H` is and the vertex types have
decidable equality. This lets `decide` handle finite questions about box products.
-/

namespace SimpleGraph

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
instance boxProd.decidableRel [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  fun _ _ => decidable_of_iff _ boxProd_adj.symm

end SimpleGraph
