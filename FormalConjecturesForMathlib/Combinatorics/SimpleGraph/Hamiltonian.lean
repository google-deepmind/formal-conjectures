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

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- `G` is uniquely Hamiltonian: it has exactly one Hamiltonian cycle.

Two Hamiltonian cycles are the same cycle when they have the same edge set. This ignores the
basepoint and the direction of the walk.

A graph on one vertex has no cycle, so it is not uniquely Hamiltonian, although it satisfies
`SimpleGraph.IsHamiltonian`. -/
def IsUniquelyHamiltonian (G : SimpleGraph V) : Prop :=
  ∃ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle ∧
    ∀ (b : V) (q : G.Walk b b), q.IsHamiltonianCycle → q.edgeSet = p.edgeSet

/-- A uniquely Hamiltonian graph is Hamiltonian. -/
theorem IsUniquelyHamiltonian.isHamiltonian [Fintype V] (hG : G.IsUniquelyHamiltonian) :
    G.IsHamiltonian :=
  fun _ ↦ let ⟨a, p, hp, _⟩ := hG; ⟨a, p, hp⟩

/-- `G` is not uniquely Hamiltonian if and only if every Hamiltonian cycle of `G` has a second
Hamiltonian cycle, one with a different edge set. -/
theorem not_isUniquelyHamiltonian_iff :
    ¬ G.IsUniquelyHamiltonian ↔ ∀ (a : V) (p : G.Walk a a), p.IsHamiltonianCycle →
      ∃ (b : V) (q : G.Walk b b), q.IsHamiltonianCycle ∧ q.edgeSet ≠ p.edgeSet := by
  simp only [IsUniquelyHamiltonian]
  push Not
  rfl

/-- A graph with at most one vertex is not uniquely Hamiltonian. -/
theorem not_isUniquelyHamiltonian_of_subsingleton [Subsingleton V] :
    ¬ G.IsUniquelyHamiltonian := by
  rintro ⟨a, p, hp, -⟩
  exact hp.isCycle.ne_nil (by
    cases p with
    | nil => rfl
    | cons h _ => exact absurd (Subsingleton.elim _ _) h.ne)

end SimpleGraph
