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
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Arboricity

This file defines `SimpleGraph.arboricity`, the minimum number of forests
needed to cover the edges of a graph.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The **arboricity** of `G` is the minimum number of forests whose edge-union
covers `G`.  Each forest is represented as a `SimpleGraph α` with `IsAcyclic`. -/
noncomputable def arboricity (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ F : Fin k → SimpleGraph α,
    (∀ i, (F i).IsAcyclic) ∧ G ≤ ⨆ i, F i}

end SimpleGraph
