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
# Edge Connectivity

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **edge connectivity** `λ(G)` is the minimum number of edges whose removal
disconnects `G` (or reduces it to a single vertex).  Formally,
  `λ(G) = min { |F| | F ⊆ E(G), G - F is disconnected }`.

For the edgeless graph or a single-vertex graph, we define `λ(G) = 0`.

## Classical bound

`λ(G) ≤ δ(G)` — the edge connectivity is at most the minimum degree.

This is a classical theorem: for any vertex `v` of minimum degree, the `δ(G)`
edges incident to `v` form a disconnecting set (removing them isolates `v`).

## WOWII-style conjecture

A Graffiti.pc lower bound relating edge connectivity to the independence number:

`α(G) ≤ n(G) - λ(G)`

where `α(G)` is the independence number and `n = |V(G)|`.  This holds because
the complement of any independent set spans at most `n - α(G)` vertices, which
must still be connected; removing all edges incident to an independent set
disconnects at most `α(G)` vertices.
-/

namespace WrittenOnTheWallII.GraphEdgeConnectivity

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **edge connectivity** `λ(G)` of a simple graph `G`.

We define it as the minimum size of a set of edges `F ⊆ E(G)` whose removal
renders `G` disconnected.  If no such set exists (i.e., `G` has ≤ 1 vertex or
is already disconnected), we define `λ(G) = 0`. -/
noncomputable def edgeConnectivity (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf { k | ∃ F : Finset (Sym2 α),
    F.card = k ∧
    (↑F : Set (Sym2 α)) ⊆ G.edgeSet ∧
    ¬ (G.deleteEdges ↑F).Connected }

/--
**Classical bound:** `λ(G) ≤ δ(G)`.

The edge connectivity is at most the minimum degree.  Removing all edges
incident to a minimum-degree vertex disconnects (or isolates) it, giving a
disconnecting set of size `δ(G)`.
-/
@[category research solved, AMS 5]
theorem edgeConnectivity_le_minDegree (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    edgeConnectivity G ≤ G.minDegree := by
  sorry

/--
**Independence-number upper bound** (WOWII-style).

For a connected graph `G`,
`α(G) + λ(G) ≤ n(G)`
i.e., `G.indepNum + edgeConnectivity G ≤ Fintype.card α`.

Intuitively, the complement of a maximum independent set induces a connected
subgraph (since `G` is connected and removing an independent set cannot alone
disconnect the rest without removing edges); a sharper version says we need at
least `λ(G)` edge removals to disconnect, so `n - α ≥ λ`.
-/
@[category research open, AMS 5]
theorem indepNum_add_edgeConnectivity_le_card (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.indepNum + edgeConnectivity G ≤ Fintype.card α := by
  sorry

-- Sanity checks

/-- `edgeConnectivity` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ edgeConnectivity G :=
  Nat.zero_le _

/-- For `K₃`, `minDegree = 2` and `edgeConnectivity ≤ 2`
(removing the two edges incident to vertex 0 disconnects it). -/
@[category test, AMS 5]
example : edgeConnectivity (⊤ : SimpleGraph (Fin 3)) ≤ 2 := by
  unfold edgeConnectivity
  apply Nat.sInf_le
  exact ⟨{s(0, 1), s(0, 2)}, by decide, by sorry, by sorry⟩

/-- `edgeConnectivity` is nonneg as a real number. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : (0 : ℝ) ≤ (edgeConnectivity G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphEdgeConnectivity
