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

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace SimpleGraph
open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The average degree of `G`. -/
noncomputable def averageDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℚ  :=
  (∑ v, (G.degree v : ℚ)) / (Fintype.card α : ℚ)

/-- The multiset of degrees of a graph. -/
def degreeMultiset (G : SimpleGraph α) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

/-- The degree sequence of a graph, sorted in nondecreasing order. -/
noncomputable def degreeSequence (G : SimpleGraph α) [DecidableRel G.Adj] : List ℕ :=
  (Finset.univ.val.map fun v : α => G.degree v).sort (· ≤ ·)

/--
The maximum number of occurrences of any term of the degree sequence of `G`.
-/
noncomputable def degreeSequenceMultiplicity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  letI degs := degreeSequence G
  (List.max? (degs.map (fun d => degs.count d))).getD 0

/-- Infinite graphs: definitions for max degree and clique number so that the maximum
degree of a graph with unbounded degree is
`∞` rather than 0.
-/
noncomputable
def edegree {V : Type*} (G : SimpleGraph V) (v : V) : ℕ∞ := (G.neighborSet v).encard

noncomputable
def emaxDegree {V : Type*} (G : SimpleGraph V) : ℕ∞ := ⨆ v, G.edegree v

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

noncomputable def S (G : SimpleGraph α) : ℝ :=
  let card := Fintype.card α
  if card < 2 then 0 else
    let degrees := Multiset.ofList (List.map (fun v => G.degree v) Finset.univ.toList)
    let sorted_degrees := degrees.sort (· ≤ ·)
    ↑((sorted_degrees[card - 2]?).getD 0)

/-- The **second-smallest degree** of `G`'s degree sequence — DeLaVina's `σ(G)`
per the WOWII definitions popup (defEntry 65): "order the degree sequence in
nondecreasing order `d₁ ≤ d₂ ≤ … ≤ dₙ`, the second smallest degree of the
sequence is the 2nd entry". For graphs with `n ≤ 1` we conventionally
return `0`. -/
noncomputable def secondSmallestDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (degreeSequence G).getD 1 0

omit [DecidableEq α] in
/-- In a nontrivial preconnected finite graph, second-smallest degree one forces two leaves. -/
lemma exists_distinct_degree_one_of_secondSmallestDegree_eq_one [Nontrivial α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Preconnected)
    (hσ : secondSmallestDegree G = 1) :
    ∃ x y : α, x ≠ y ∧ G.degree x = 1 ∧ G.degree y = 1 := by
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Fintype.one_lt_card (α := α)
  obtain ⟨a, b, tail, hds⟩ : ∃ a b tail, ds = a :: b :: tail := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a rest =>
        cases hrest : rest with
        | nil => simp [h, hrest] at hlen
        | cons b tail => exact ⟨a, b, tail, rfl⟩
  have hb : b = 1 := by
    simpa [secondSmallestDegree, ds, hds] using hσ
  have hsorted : ds.Pairwise (· ≤ ·) := by
    simp [ds, degreeSequence]
  have hab : a ≤ b := by
    simpa [hds] using hsorted.rel_get_of_lt (a := ⟨0, by simp [hds]⟩)
      (b := ⟨1, by simp [hds]⟩) (by simp)
  have ha_mem : a ∈ ds := by
    simp [hds]
  have ha_pos : 0 < a := by
    have ha_map : a ∈ Finset.univ.val.map (fun v : α => G.degree v) := by
      simpa [ds, degreeSequence] using ha_mem
    obtain ⟨v, -, rfl⟩ := Multiset.mem_map.mp ha_map
    exact hG.degree_pos_of_nontrivial v
  have ha : a = 1 := by
    omega
  have hcount : 2 ≤ ds.count 1 := by
    simp [hds, ha, hb]
  have hcoeds : (↑ds : Multiset ℕ) =
      Finset.univ.val.map (fun v : α => G.degree v) := by
    simp [ds, degreeSequence]
  have hcountm :
      2 ≤ (Finset.univ.val.map (fun v : α => G.degree v)).count 1 := by
    rw [← hcoeds, Multiset.coe_count]
    exact hcount
  have hleaves : 2 ≤ (Finset.univ.filter fun v : α => G.degree v = 1).card := by
    rw [Multiset.count_map] at hcountm
    simpa only [← Finset.filter_val, eq_comm] using hcountm
  have htwo : 1 < (Finset.univ.filter fun v : α => G.degree v = 1).card := by
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp htwo
  exact ⟨x, y, hxy, (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
/-- The number of triangles (3-cliques) of `G` incident to vertex `v`:
the number of 3-element cliques containing `v`. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

/-- The length of a graph: the square root of the sum of the squares of degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

/-- The number of vertices of degree k in `G`. -/
def countDegreeK (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = k)).card

end SimpleGraph
