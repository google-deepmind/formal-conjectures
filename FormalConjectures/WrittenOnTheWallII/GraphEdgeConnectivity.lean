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
module

public import FormalConjecturesUtil
/-!
# Edge Connectivity

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphEdgeConnectivity

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

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
**Independence-number upper bound.**

For a connected graph `G`,
`α(G) + λ(G) ≤ n(G)`
i.e., `G.indepNum + edgeConnectivity G ≤ Fintype.card α`.

The minimum degree is at most `n - α`: a vertex of a maximum independent set
has neighbours only outside that set. Combine this with `λ(G) ≤ δ(G)`.
-/
@[category textbook, AMS 5]
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
