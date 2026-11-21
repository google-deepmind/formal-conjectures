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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Prod

/-!
# Boundaries in finite graphs

The edge boundary consists of edges directed from a vertex set to its complement. The inner
vertex boundary consists of the vertices in the set that have a neighbor outside it.
-/

@[expose] public section

namespace SimpleGraph

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge boundary of $A$, with each crossing edge oriented from $A$ to its complement.
Each undirected crossing edge occurs exactly once. -/
def edgeBoundary (A : Finset V) : Finset (V × V) :=
  {p ∈ A ×ˢ Aᶜ | G.Adj p.1 p.2}

/-- The inner vertex boundary of $A$: vertices in $A$ with a neighbor outside $A$. -/
def innerVertexBoundary (A : Finset V) : Finset V :=
  {v ∈ A | ∃ w ∉ A, G.Adj v w}

@[simp]
theorem edgeBoundary_empty : G.edgeBoundary ∅ = ∅ := by
  simp [edgeBoundary]

@[simp]
theorem edgeBoundary_univ : G.edgeBoundary Finset.univ = ∅ := by
  simp [edgeBoundary]

@[simp]
theorem innerVertexBoundary_empty : G.innerVertexBoundary ∅ = ∅ := by
  simp [innerVertexBoundary]

@[simp]
theorem innerVertexBoundary_univ : G.innerVertexBoundary Finset.univ = ∅ := by
  simp [innerVertexBoundary]

end SimpleGraph
