/-
Copyright 2025 The Formal Conjectures Authors.

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

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Real.Archimedean

namespace SimpleGraph

open Finset
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `Ls G` is the maximum number of leaves over all spanning trees of `G`.
It is defined to be `0` when `G` is not connected. -/
noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)

/-- `n G` is the number of vertices of `G` as a real number. -/
noncomputable def n (_ : SimpleGraph α) : ℝ := Fintype.card α

/-- `m G` is the size of a maximum matching of `G`. -/
noncomputable def m (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => (M.edgeSet.toFinset.card : ℝ)) matchings)

/-- The independence number of a graph `G`. -/
noncomputable def a (G : SimpleGraph α) : ℝ := (G.indepNum : ℝ)

/-- The maximum cardinality among all independent sets `s`
    that maximize the quantity `|s| - |N(s)|`, where `N(s)`
    is the neighborhood of the set `s`. -/
noncomputable def aprime (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  letI indep_sets : Finset (Finset α) := univ.powerset.filter (fun s => G.IsIndepSet (s : Set α))
  letI diff (s : Finset α) : ℤ := (s.card : ℤ) - (⋃ v ∈ (s : Set α), G.neighborSet v).toFinset.card
  letI max_diff := (indep_sets.image diff).max
  letI critical_sets := indep_sets.filter (fun s ↦ diff s = max_diff.getD 0)
  letI max_card := (critical_sets.image Finset.card).max
  (max_card.getD 0 : ℝ)


/-- `largestInducedForestSize G` is the size of a largest induced forest of `G`. -/
noncomputable def largestInducedForestSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsAcyclic ∧ s.card = n }

/-- `f G` is the number of vertices of a largest induced forest of `G` as a real. -/
noncomputable def f (G : SimpleGraph α) : ℝ :=
  (largestInducedForestSize G : ℝ)

/-- `largestInducedBipartiteSubgraphSize G` is the size of a largest induced
bipartite subgraph of `G`. -/
noncomputable def largestInducedBipartiteSubgraphSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, (G.induce s).IsBipartite ∧ s.card = n }

/-- `b G` is the number of vertices of a largest induced bipartite subgraph of `G`.
Returned as a real number. -/
noncomputable def b (G : SimpleGraph α) : ℝ :=
  (largestInducedBipartiteSubgraphSize G : ℝ)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/-- The same quantity as a real number. -/
noncomputable def indepNeighbors (G : SimpleGraph α) (v : α) : ℝ :=
  (indepNeighborsCard G v : ℝ)

/-- Average of `indepNeighbors` over all vertices. -/
noncomputable def averageIndepNeighbors (G : SimpleGraph α) : ℝ :=
  (∑ v ∈ Finset.univ, indepNeighbors G v) / (Fintype.card α : ℝ)

end SimpleGraph
