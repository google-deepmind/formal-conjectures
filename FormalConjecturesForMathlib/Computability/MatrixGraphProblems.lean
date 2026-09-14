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

public import FormalConjecturesForMathlib.Computability.BitstringEncoding
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Perm

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

open BitstringEncoding

/-- Row-major finite adjacency data, encoded by the existing nested-list bitstring instance. -/
abbrev Code := List (List Bool)

/-- Missing entries default to false; well-formedness is checked separately in each problem. -/
def entry (a : Code) (i j : Fin a.length) : Bool :=
  ((a[i.val]?.getD [])[j.val]?).getD false

def Square (a : Code) : Prop := ∀ row ∈ a, row.length = a.length

/-- Each Boolean in a list occupies a three-bit self-delimiting block. -/
theorem encoded_row_length (row : List Bool) : (bitEncode row).length = 3 * row.length := by
  induction row with
  | nil => rfl
  | cons b row ih =>
    change (delimit (bitEncode b) ++ bitEncode row).length = 3 * (row.length + 1)
    rw [List.length_append, length_delimit, ih]
    change 2 * 1 + 1 + 3 * row.length = _
    omega

theorem encoded_matrix_length (a : Code) (n : ℕ) (h : ∀ row ∈ a, row.length = n) :
    (bitEncode a).length = a.length * (6 * n + 1) := by
  induction a with
  | nil => change 0 = 0 * (6 * n + 1); simp
  | cons row a ih =>
    change (delimit (bitEncode row) ++ bitEncode a).length = (a.length + 1) * (6 * n + 1)
    rw [List.length_append, length_delimit, encoded_row_length,
      ih (fun r hr ↦ h r (by simp [hr])), h row (by simp), Nat.add_mul, one_mul]
    omega

/-- A square input explicitly occupies a quadratic number of bits in its vertex count. -/
theorem encoded_square_length (a : Code) (h : Square a) :
    (bitEncode a).length = a.length * (6 * a.length + 1) :=
  encoded_matrix_length a a.length h

def ValidDigraph (a : Code) : Prop :=
  Square a ∧ ∀ i : Fin a.length, entry a i i = false

def ValidGraph (a : Code) : Prop :=
  ValidDigraph a ∧ ∀ i j : Fin a.length, entry a i j = entry a j i

instance (a : Code) : Decidable (ValidDigraph a) := by
  unfold ValidDigraph Square
  infer_instance

instance (a : Code) : Decidable (ValidGraph a) := by
  unfold ValidGraph
  infer_instance

/-- The directed adjacency relation, retaining orientation. -/
def toDigraph (a : Code) : Digraph (Fin a.length) :=
  Digraph.mk' (entry a)

/-- For a valid symmetric input, this is exactly its encoded simple graph. -/
def toGraph (a : Code) : SimpleGraph (Fin a.length) :=
  SimpleGraph.fromRel (fun i j ↦ entry a i j = true)

instance (a : Code) : DecidableRel (toGraph a).Adj := by
  unfold toGraph SimpleGraph.fromRel
  infer_instance

theorem toGraph_adj {a : Code} (h : ValidGraph a) (i j : Fin a.length) :
    (toGraph a).Adj i j ↔ entry a i j = true := by
  change (i ≠ j ∧ (entry a i j = true ∨ entry a j i = true)) ↔ _
  rw [h.2 j i, or_self]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_, he⟩
    rintro rfl
    rw [h.1.2 i] at he
    cases he

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

/-- Cyclic successor on a finite nonempty index type; an argument itself witnesses nonemptiness. -/
def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- A cyclic ordering containing every vertex exactly once, following directed edges. -/
def HasSpanningCycle (a : Code) : Prop :=
  ∃ order : Equiv.Perm (Fin a.length),
    ∀ i, (toDigraph a).Adj (order i) (order (next i))

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
    ∀ i, entry a (order i) (order (next i)) = true)
  infer_instance

instance (a : Code) : Decidable (DirectedHamiltonian a) := by
  unfold DirectedHamiltonian
  infer_instance

instance (a : Code) : Decidable (UndirectedHamiltonian a) := by
  unfold UndirectedHamiltonian
  infer_instance

end Computability.MatrixGraph
