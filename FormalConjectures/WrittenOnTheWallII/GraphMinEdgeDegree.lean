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

import FormalConjectures.Util.ProblemImports

/-!
# Graph Minimum Edge Degree Conjecture

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **minimum edge degree** (or *minimum degree of an edge*) of a graph `G`
is defined as
  `minEdgeDegree G = min_{uv ∈ E(G)} min(deg(u), deg(v))`
i.e., the smallest value of the minimum endpoint degree over all edges.
It equals 0 on the edgeless graph (no edges), and is at least 1 for any graph
with an edge.

## Conjecture

We state a Graffiti.pc–style conjecture:
for a connected graph `G`, the independence number satisfies
`α(G) ≥ n(G) / (1 + minEdgeDegree(G))`.

This is a strengthening of the greedy bound `α ≥ n / (1 + Δ)` since
`minEdgeDegree ≤ δ ≤ Δ`.
-/

namespace WrittenOnTheWallII.GraphMinEdgeDegree

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **minimum edge degree** of `G` is the minimum over all edges `uv` of
`min(deg(u), deg(v))`.  Returns 0 if `G` has no edges. -/
noncomputable def minEdgeDegree (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if h : G.edgeFinset.Nonempty then
    G.edgeFinset.inf' h (fun e =>
      e.lift ⟨fun u v => min (G.degree u) (G.degree v), fun u v => by simp [min_comm]⟩)
  else 0

/-- For a connected graph `G`, the independence number satisfies
`α(G) ≥ n(G) / (1 + minEdgeDegree(G))`.

This refines the classical bound `α(G) ≥ n / (Δ + 1)` by replacing the maximum
degree `Δ` with the smaller quantity `minEdgeDegree(G)`. -/
@[category research open, AMS 5]
theorem indepNum_lower_bound_minEdgeDegree (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    Fintype.card α / (1 + minEdgeDegree G) ≤ G.indepNum := by
  sorry

-- Sanity checks

/-- In `K₃`, every edge has both endpoints of degree 2, so `minEdgeDegree K₃ = 2`. -/
@[category test, AMS 5]
example : minEdgeDegree (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold minEdgeDegree
  native_decide

/-- In the path `P₃` (edges 0–1 and 1–2), the edge 0–1 has min endpoint degree
`min(deg 0, deg 1) = min(1, 2) = 1`, so `minEdgeDegree P₃ = 1`. -/
@[category test, AMS 5]
example : minEdgeDegree
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 1 := by
  unfold minEdgeDegree
  native_decide

/-- In the star `K₁₃` (center 0, leaves 1, 2, 3), every edge has one endpoint of
degree 1, so `minEdgeDegree K₁₃ = 1`. -/
@[category test, AMS 5]
example : minEdgeDegree
    (SimpleGraph.fromEdgeSet {s(0,1), s(0,2), s(0,3)} : SimpleGraph (Fin 4)) = 1 := by
  unfold minEdgeDegree
  native_decide

end WrittenOnTheWallII.GraphMinEdgeDegree
