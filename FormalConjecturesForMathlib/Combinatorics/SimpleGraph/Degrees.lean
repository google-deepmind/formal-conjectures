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

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace SimpleGraph

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
  open scoped Classical in
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

/-- The maximum over all degrees `d` of `countDegreeK G d`.
This is the frequency of the most-common degree value (mode frequency). -/
def maxDegreeCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.range (Fintype.card α + 1)).sup (countDegreeK G)

/-- The smallest degree value achieving the mode frequency.
This is defined via `sInf` on the (nonempty when the graph has vertices) set of
modal degrees.  When the graph has no vertices this set may be empty; the
`sInf ℕ` convention then yields 0. -/
noncomputable def modeDegreeMin (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf {d | countDegreeK G d = maxDegreeCount G}

/-- The largest degree value achieving the mode frequency.
Defined as the supremum of the set of modal degree values (those `d` for which
`countDegreeK G d = maxDegreeCount G`).  When the graph has no vertices the set
may be empty; by convention `sSup ℕ ∅ = 0`. -/
noncomputable def modeDegreeMax (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup {d | countDegreeK G d = maxDegreeCount G}

/-- The number of vertices whose degree equals `modeDegreeMin G` **and** is even.
When `modeDegreeMin G` is odd, every vertex counted by `modeDegreeMin G` has an
odd degree, so `evenModeMinCount G = 0`. -/
noncomputable def evenModeMinCount (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = modeDegreeMin G ∧ Even (G.degree v))).card

/-- The **median degree** of `G`.

We form the list of degrees of all vertices, sort it in non-decreasing order, and
return the element at position `Fintype.card α / 2`.  When the graph has no
vertices the degree list is empty; we return 0 in that case. -/
noncomputable def medianDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if Fintype.card α = 0 then 0
  else
    let degList : List ℕ := Finset.univ.toList.map (fun v => G.degree v)
    let sorted : List ℕ := degList.mergeSort (· ≤ ·)
    sorted.getD (Fintype.card α / 2) 0

/-- The **minimum edge degree** of `G` is the minimum over all edges `uv` of
`min(deg(u), deg(v))`.  Returns 0 if `G` has no edges. -/
noncomputable def minEdgeDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if h : G.edgeFinset.Nonempty then
    G.edgeFinset.inf' h (fun e =>
      e.lift ⟨fun u v => min (G.degree u) (G.degree v), fun u v => by simp [min_comm]⟩)
  else 0

end SimpleGraph
