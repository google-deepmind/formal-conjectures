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

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Finite tree recognition
-/

@[expose] public section

namespace SimpleGraph

/-- Finite tree recognition using connectivity and the exact edge count. -/
instance decidableIsTree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable G.IsTree :=
  decidable_of_iff (G.Connected ∧ G.edgeFinset.card + 1 = Fintype.card V) (by
    rw [isTree_iff_connected_and_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, edgeFinset_card])

end SimpleGraph
