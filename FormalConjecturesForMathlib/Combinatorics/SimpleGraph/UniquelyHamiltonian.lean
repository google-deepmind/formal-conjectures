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

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian


@[expose] public section

/-!
# Uniquely Hamiltonian

A simple Graph `G` is *uniquely Hamiltonian* if it contains exactly one Hamiltonian cycle.
This file defines `SimpleGraph.IsUniquelyHamiltonian` in terms of edge deletion: `G` has a
Hamiltonian cycle `p`, and deleting any single edge of `p` destroys all Hamiltonian cycles of `G`.
-/
namespace SimpleGraph
variable {V: Type*} [DecidableEq V] (G : SimpleGraph V)

/-- `G` is uniquely Hamiltonian: it has a Hamiltonian cycle `p`, and deleting any edge of `p`
destroys all Hamiltonian cycles. -/
def IsUniquelyHamiltonian : Prop :=
  ∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle ∧
    ∀ e ∈ p.edges, ¬ (∃ (b : V) (q : (G.deleteEdges {e}).Walk b b),
    q.IsHamiltonianCycle)

end SimpleGraph
