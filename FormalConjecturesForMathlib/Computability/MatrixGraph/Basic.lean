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
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Binary adjacency matrices for finite graphs

Rows declare the vertex count, including isolated vertices. Square shape, absence
of loops and symmetry are explicit validity predicates. Conversion to a simple
graph agrees with the matrix on valid inputs.

*References:*
* Karp, *Reducibility among Combinatorial Problems* (1972), §4:
  https://doi.org/10.1007/978-1-4684-2001-2_9.
-/

@[expose] public section

namespace Computability.MatrixGraph

/-- Row-major finite adjacency data, encoded by the existing nested-list bitstring instance. -/
abbrev Code := List (List Bool)

/-- Missing entries default to false; well-formedness is checked separately in each problem. -/
def entry (a : Code) (i j : Fin a.length) : Bool :=
  ((a[i.val]?.getD [])[j.val]?).getD false

/-- Every row has exactly the declared vertex count, including the empty matrix. -/
def Square (a : Code) : Prop := ∀ row ∈ a, row.length = a.length

/-- A square adjacency matrix with no loops; orientation is unrestricted. -/
def ValidDigraph (a : Code) : Prop :=
  Square a ∧ ∀ i : Fin a.length, entry a i i = false

/-- A loopless square adjacency matrix symmetric across its diagonal. -/
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

end Computability.MatrixGraph
