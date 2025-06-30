import FormalConjectures.GraphConjectures.Imports

namespace SimpleGraph

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `Ls G` is the maximum number of leaves over all spanning trees of `G`.
It is defined to be `0` when `G` is not connected. -/
noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  if h : G.Connected then
    let spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
    let leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
    let num_leaves (T : Subgraph G) := (leaves T).card
    sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)
  else
    0

/-- `n G` is the number of vertices of `G` as a real number. -/
noncomputable def n (_ : SimpleGraph α) : ℝ := Fintype.card α

/-- `m G` is the size of a maximum matching of `G`. -/
noncomputable def m (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let matchings := { M : Subgraph G | M.IsMatching }
  sSup (Set.image (fun M => (M.edgeSet.toFinset.card : ℝ)) matchings)

/-- `a G` is a quantity defined via independent sets used in Conjecture 6. -/
noncomputable def a (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  let independent_sets := { S : Finset α | IsIndepSet G S }
  if h_indep : independent_sets.Nonempty then
    let f (S : Finset α) : ℤ := (S.card : ℤ) - (S.biUnion (fun v => G.neighborFinset v)).card
    let f_values_real : Set ℝ := Set.image (fun s => (f s : ℝ)) independent_sets
    if h_fvals : f_values_real.Nonempty then
      let max_val := sSup f_values_real
      let critical_independent_sets := { S | S ∈ independent_sets ∧ (f S : ℝ) = max_val }
      if h_crit : critical_independent_sets.Nonempty then
        sSup (Set.image (fun S => (S.card : ℝ)) critical_independent_sets)
      else 0
    else 0
  else 0

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

