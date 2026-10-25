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
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

variable {V : Type*}

/-- The vertices of `G` can be covered by at most `k` paths of `G`. The paths are not required to
be vertex-disjoint, and a single vertex counts as a path. -/
def HasPathCover (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (P : Fin m → (u : V) × (v : V) × G.Walk u v), m ≤ k ∧
    (∀ i, (P i).2.2.IsPath) ∧ ∀ x : V, ∃ i, x ∈ (P i).2.2.support

end SimpleGraph
