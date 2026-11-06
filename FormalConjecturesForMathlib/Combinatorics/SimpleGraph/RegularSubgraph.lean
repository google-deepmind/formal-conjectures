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

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Subgraph
public import Mathlib.Data.Real.Basic

/-!
# Regular subgraphs and degree criticality
-/

@[expose] public section

namespace SimpleGraph

/-- `G` contains a nonempty (not necessarily induced or spanning) `k`-regular subgraph. -/
def ContainsRegularSubgraph {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧ H.verts.Finite ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

open scoped Classical in
/--
`G` contains a non-trivial (neither empty nor complete) regular induced subgraph on at least
`L` vertices.
-/
def HasLargeNontrivialRegularInduced {V : Type*} [Fintype V] (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (S : Finset V) (d : ℕ), L ≤ S.card ∧ 0 < d ∧ d + 1 < S.card ∧ (G.induce S).IsRegularOfDegree d

open scoped Classical in
/--
A graph on `n` vertices is *degree $3$ critical* if it has `2n - 2` edges and every proper
induced subgraph has minimum degree `≤ 2`.
-/
def IsDegreeThreeCritical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.edgeSet.ncard = 2 * Fintype.card V - 2 ∧
    ∀ s : Set V, s ≠ Set.univ → (G.induce s).minDegree ≤ 2

/--
A predicate that holds if $S$ is a regular induced subgraph of $G$
-/
def Subgraph.IsRegularInduced {V : Type*} [Fintype V] {G : SimpleGraph V} (S : Subgraph G) : Prop :=
  open scoped Classical in
  S.IsInduced ∧ ∃ k, (S.coe).IsRegularOfDegree k

end SimpleGraph
