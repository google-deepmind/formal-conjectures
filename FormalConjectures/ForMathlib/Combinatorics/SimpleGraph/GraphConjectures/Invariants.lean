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

import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions
import FormalConjectures.ForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Domination
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.CompletePartialOrder

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Abbreviation for the average independence number of the neighborhoods. -/
noncomputable abbrev l (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- The same quantity under a different name, used in some conjectures. -/
noncomputable abbrev l_avg (G : SimpleGraph α) : ℝ := averageIndepNeighbors G

/-- Independent domination number of `G`. -/
noncomputable def gi (G : SimpleGraph α) : ℕ := G.indepDominationNumber

/-- `temp_v G v = deg(v)/(n(G) - deg(v))`. -/
noncomputable def temp_v (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℝ :=
  let n := Fintype.card α
  let deg := G.degree v
  if n = deg then 0 else (deg : ℝ) / ((n : ℝ) - (deg : ℝ))

/-- Maximum of `temp_v` over all vertices. -/
noncomputable def MaxTemp (G : SimpleGraph α) [DecidableRel G.Adj] [Fintype α] [Nonempty α] : ℝ :=
  let temps := Finset.univ.image (temp_v G)
  temps.max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- Cardinality of the union of the neighbourhoods of the ends of the non-edge `e`. -/
def non_edge_neighborhood_card (G : SimpleGraph α) [DecidableRel G.Adj] (e : Sym2 α) : ℕ :=
  Sym2.lift ⟨fun u v => (G.neighborFinset u ∪ G.neighborFinset v).card,
    fun u v => by simp [Finset.union_comm]⟩ e

/-- Minimum size of the neighbourhood of a non-edge of `G`. -/
noncomputable def NG (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let non_edges := (compl G).edgeFinset
  if h : non_edges.Nonempty then
    let neighbor_sizes := non_edges.image (non_edge_neighborhood_card G)
    (neighbor_sizes.min' (Finset.Nonempty.image h _))
  else
    (Fintype.card α : ℝ)

/-- Size of a largest induced forest of `G` expressed as a real number. -/
noncomputable def S (G : SimpleGraph α) : ℝ :=
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := Multiset.sort (·≤·) degrees
    ↑((sorted_degrees[card - 2]?).getD 0)

/-- Local eccentricity of a vertex. -/
noncomputable def local_eccentricity (G : SimpleGraph α) (v : α) : ENat :=
  sSup (Set.range (G.edist v))

/-- The largest integer less than or equal to `x`. -/
noncomputable def FLOOR (x : ℝ) : ℝ := ⌊x⌋

/-- Eccentricity of a vertex. -/
noncomputable def eccentricity (G : SimpleGraph α) (v : α) : ℕ∞ :=
  sSup (Set.range (G.edist v))

/-- The minimum eccentricity among all vertices. -/
noncomputable def minEccentricity (G : SimpleGraph α) : ℕ∞ :=
  sInf (Set.range (eccentricity G))

/-- The set of vertices of minimum eccentricity. -/
noncomputable def graphCenter (G : SimpleGraph α) : Set α :=
  {v : α | eccentricity G v = minEccentricity G}

/-- The maximum eccentricity among all vertices. -/
noncomputable def maxEccentricity (G : SimpleGraph α) : ℕ∞ :=
  sSup (Set.range (eccentricity G))

/-- The set of vertices of maximum eccentricity. -/
noncomputable def maxEccentricityVertices (G : SimpleGraph α) : Set α :=
  {v : α | eccentricity G v = maxEccentricity G}

/-- Distance from a vertex to a finite set. -/
noncomputable def distToSet (G : SimpleGraph α) (v : α) (S : Set α) : ℕ :=
  if h : S.toFinset.Nonempty then
    (S.toFinset.image (fun s => G.dist v s)).min' (Finset.Nonempty.image h _)
  else 0

/-- Average distance of `G`. -/
noncomputable def averageDistance (G : SimpleGraph α) : ℝ :=
  if Fintype.card α > 1 then
    (∑ u ∈ Finset.univ, ∑ v ∈ Finset.univ, (G.dist u v : ℝ)) /
      ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))
  else
    0

/-- The floor of the average distance of `G`. -/
noncomputable def path (G : SimpleGraph α) : ℕ :=
  if G.Connected then
    Nat.floor (averageDistance G)
  else
    0

/-- Auxiliary quantity `ecc` used in conjecture 34. -/
noncomputable def ecc (G : SimpleGraph α) (S : Set α) : ℕ :=
  let s_comp := Finset.univ.filter (fun v => v ∉ S)
  if h : s_comp.Nonempty then
    (s_comp.image (fun v => distToSet G v S)).max' (Finset.Nonempty.image h _)
  else 0

/-- Average distance from all vertices to a given set. -/
noncomputable def distavg (G : SimpleGraph α) (S : Set α) : ℝ :=
  if Fintype.card α > 0 then
    (∑ v ∈ Finset.univ, (distToSet G v S : ℝ)) / (Fintype.card α : ℝ)
  else
    0

/-- A family of paths covering all vertices without overlaps. -/
def IsPathCover (G : SimpleGraph α) (P : Finset (Finset α)) : Prop :=
  (∀ s1 ∈ P, ∀ s2 ∈ P, s1 ≠ s2 → Disjoint s1 s2) ∧
  (Finset.univ ⊆ P.biUnion id) ∧
  (∀ s ∈ P, ∃ (u v : α) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset)

/-- Minimum size of a path cover of `G`. -/
noncomputable def pathCoverNumber (G : SimpleGraph α) : ℕ :=
  sInf { k | ∃ P : Finset (Finset α), P.card = k ∧ IsPathCover G P }

/-- The same quantity as a real number. -/
noncomputable def p (G : SimpleGraph α) : ℝ := (pathCoverNumber G : ℝ)

end SimpleGraph
