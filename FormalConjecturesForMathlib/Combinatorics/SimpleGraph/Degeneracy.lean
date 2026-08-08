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

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# Degeneracy

This file defines `SimpleGraph.degeneracy`, the maximum over all nonempty
induced subgraphs of the minimum degree.
-/

namespace SimpleGraph

open Classical in
/-- The **degeneracy** of `G`: the maximum, over all nonempty induced subgraphs `H`,
of the minimum degree of `H`.

We take the supremum over all nonempty vertex subsets `S : Finset α` of
`minDegree(G[S])`.  For the empty set we contribute 0 so the `sup` is over a
nonempty domain (`Finset.univ` includes `∅`). -/
noncomputable def degeneracy {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) : ℕ :=
  Finset.univ.sup (fun S : Finset α =>
    if S.Nonempty then (G.induce (S : Set α)).minDegree else 0)

end SimpleGraph
