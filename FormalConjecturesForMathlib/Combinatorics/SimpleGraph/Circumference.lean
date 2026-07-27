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

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Nat.Lattice

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `circumference G` is the length of the longest cycle in `G`.
    It is `0` when `G` is acyclic. -/
noncomputable def circumference (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n : ℕ | ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ w.length = n }

end SimpleGraph
