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

public import FormalConjecturesForMathlib.Computability.MatrixGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Finite matrix inputs for graph decision problems

The number of rows declares the vertex count. Valid directed inputs are square and loopless;
valid undirected inputs are also symmetric. Thus isolated vertices are explicitly represented.
Malformed matrices and zero decision parameters are rejected, not silently repaired.

Cycles are represented by a permutation of the vertices with cyclic successor edges.
We require at least two vertices for a directed cycle and three for an undirected cycle.
The definitions concern decision problems from Karp, *Reducibility among Combinatorial
Problems* (1972), §4, https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

@[expose] public section

namespace Computability.MatrixGraph

/-- A clique with exactly the requested positive number of vertices. -/
def Clique (input : Code × ℕ) : Prop :=
  ValidGraph input.1 ∧ 0 < input.2 ∧
    ∃ s : Finset (Fin input.1.length), s.card = input.2 ∧ (toGraph input.1).IsClique s

/-- A vertex cover with at most the requested positive bound. -/
def VertexCover (input : Code × ℕ) : Prop :=
  ValidGraph input.1 ∧ 0 < input.2 ∧
    ∃ s : Finset (Fin input.1.length), s.card ≤ input.2 ∧
      (toGraph input.1).IsVertexCover s

/-- A proper coloring using a palette of the requested positive size. -/
def Colorable (input : Code × ℕ) : Prop :=
  ValidGraph input.1 ∧ 0 < input.2 ∧
    ∃ color : Fin input.1.length → Fin input.2,
      ∀ i j, (toGraph input.1).Adj i j → color i ≠ color j

theorem colorable_iff (a : Code) (k : ℕ) :
    Colorable (a, k) ↔ ValidGraph a ∧ 0 < k ∧ (toGraph a).Colorable k := by
  constructor
  · rintro ⟨ha, hk, color, hc⟩
    exact ⟨ha, hk, ⟨SimpleGraph.Coloring.mk color (fun {i j} ↦ hc i j)⟩⟩
  · rintro ⟨ha, hk, ⟨color⟩⟩
    exact ⟨ha, hk, color, fun _ _ h ↦ color.valid h⟩

/-- A cyclic ordering containing every vertex exactly once, following directed edges. -/
def HasSpanningCycle (a : Code) : Prop :=
  ∃ order : Equiv.Perm (Fin a.length),
    ∀ i, (toDigraph a).Adj (order i) (order (finRotate a.length i))

/-- Directed Hamiltonian cycles may have two vertices but not zero or one. -/
def DirectedHamiltonian (a : Code) : Prop :=
  ValidDigraph a ∧ 2 ≤ a.length ∧ HasSpanningCycle a

/-- Undirected cycles have at least three vertices; traversing one edge twice is not a cycle. -/
def UndirectedHamiltonian (a : Code) : Prop :=
  ValidGraph a ∧ 3 ≤ a.length ∧ HasSpanningCycle a

instance (input : Code × ℕ) : Decidable (Clique input) := by
  unfold Clique
  infer_instance

instance (input : Code × ℕ) : Decidable (VertexCover input) := by
  unfold VertexCover SimpleGraph.IsVertexCover
  infer_instance

instance (input : Code × ℕ) : Decidable (Colorable input) := by
  unfold Colorable
  infer_instance

instance (a : Code) : Decidable (HasSpanningCycle a) := by
  change Decidable (∃ order : Equiv.Perm (Fin a.length),
    ∀ i, entry a (order i) (order (finRotate a.length i)) = true)
  infer_instance

instance (a : Code) : Decidable (DirectedHamiltonian a) := by
  unfold DirectedHamiltonian
  infer_instance

instance (a : Code) : Decidable (UndirectedHamiltonian a) := by
  unfold UndirectedHamiltonian
  infer_instance

end Computability.MatrixGraph
