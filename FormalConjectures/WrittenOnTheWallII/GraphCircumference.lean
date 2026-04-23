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
# Graph Circumference Conjecture

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **circumference** of a graph `G` is the length (number of edges) of a
longest cycle in `G`.  If `G` is acyclic (a forest), the circumference is
defined to be 0.

## Conjecture

A classical result due to Dirac (1952) states that every 2-connected graph
satisfies `circumference(G) ≥ 2 · δ(G)` where `δ(G)` is the minimum degree.
We state it as a conjecture in the Graffiti.pc style.
-/

namespace WrittenOnTheWallII.GraphCircumference

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **circumference** of `G` is the length of a longest cycle.
It equals 0 for acyclic graphs (forests). -/
noncomputable def circumference (G : SimpleGraph α) : ℕ :=
  sSup ({0} ∪ {k | ∃ v : α, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = k})

/-- The vertex connectivity `κ(G)`: the minimum number of vertices whose removal
disconnects the graph (or `n - 1` when the graph is complete).
Vertex connectivity is not yet in Mathlib; we define it here as the minimum size of
a vertex separator, where removing `S` leaves the induced subgraph on `Sᶜ` disconnected.
-- TODO: replace with a Mathlib definition when one becomes available. -/
noncomputable def vertexConnectivity (G : SimpleGraph α) : ℕ :=
  if Fintype.card α ≤ 1 then 0
  else sInf { k | ∃ S : Finset α, S.card = k ∧
    (¬(G.induce (↑Sᶜ : Set α)).Connected ∨ S.card = Fintype.card α - 1) }

/-- Dirac's theorem (1952): Every 2-connected graph `G` on `n ≥ 3` vertices
satisfies `circumference(G) ≥ 2 · δ(G)`.
Here `δ(G) = G.minDegree` is the minimum degree and 2-connectivity means
`vertexConnectivity G ≥ 2`. -/
@[category research solved, AMS 5]
theorem dirac_circumference (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : 2 ≤ vertexConnectivity G) :
    2 * G.minDegree ≤ circumference G := by
  sorry

-- Sanity checks

/-- The circumference of `K₃` is 3 (the triangle itself is a 3-cycle). -/
@[category test, AMS 5]
example : circumference (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold circumference
  sorry

/-- The circumference of the 4-cycle `C₄` is 4. -/
@[category test, AMS 5]
example : circumference (SimpleGraph.fromEdgeSet
    {s(0,1), s(1,2), s(2,3), s(3,0)} : SimpleGraph (Fin 4)) = 4 := by
  unfold circumference
  sorry

/-- For a path `P₃` (which is acyclic), the circumference is 0. -/
@[category test, AMS 5]
example : circumference
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 0 := by
  unfold circumference
  sorry

end WrittenOnTheWallII.GraphCircumference
