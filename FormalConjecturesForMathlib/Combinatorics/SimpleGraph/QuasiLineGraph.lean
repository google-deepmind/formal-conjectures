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

public import Mathlib.Combinatorics.SimpleGraph.Clique
@[expose] public section

namespace SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical Finset List

/-- A graph is a quasi-line graph if the neighborhood of every vertex can be partitioned into two cliques. -/
def IsQuasiLineGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ (s₁ s₂ : Set V),
    s₁ ∪ s₂ = G.neighborSet v ∧ G.IsClique s₁ ∧ G.IsClique s₂


end SimpleGraph
