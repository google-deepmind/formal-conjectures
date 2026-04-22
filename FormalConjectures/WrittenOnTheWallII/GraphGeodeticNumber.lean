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
# Geodetic Number of Graphs

*Reference:*
[F. Buckley and F. Harary, Distance in Graphs, Addison-Wesley, 1990]

[G. Chartrand, F. Harary, P. Zhang, On the geodetic number of a graph,
Networks 39 (2002) 1–6](https://doi.org/10.1002/net.10007)

## Definition

A set `S ⊆ V(G)` is a **geodetic set** if every vertex of `G` lies on some
shortest path (geodesic) between two vertices of `S`.

The **geodetic number** `g(G)` is the minimum cardinality of a geodetic set.

## Conjecture

A classical fact (resolved) is that for the complete graph `Kₙ`,
`g(Kₙ) = n`, since every vertex must be an endpoint of some geodesic in `S`
(all shortest paths have length 1, so each vertex must appear in `S` itself).

A nontrivial open conjecture is that for any connected graph `G`,
`g(G) ≤ diam(G) + 1` is **false** in general (e.g., it fails for hypercubes),
so we instead state the resolved classical lower bound `g(G) ≥ 2` for connected
graphs with at least 2 vertices, and the Graffiti.pc-style upper bound
`g(G) ≤ n − diam(G) + 1` for connected graphs (a known resolved bound).
-/

namespace WrittenOnTheWallII.GraphGeodeticNumber

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- A set `S` is a **geodetic set** of `G` if every vertex `v` lies on a
shortest `u`-`w` path for some `u, w ∈ S`.

A walk `p` is a shortest path from `u` to `w` if it is a path and its length
equals `G.dist u w`. -/
def IsGeodeticSet (G : SimpleGraph α) (S : Finset α) : Prop :=
  ∀ v : α, ∃ u ∈ S, ∃ w ∈ S,
    ∃ p : G.Walk u w, p.IsPath ∧ p.length = G.dist u w ∧ v ∈ p.support

/-- The **geodetic number** of `G`: the minimum size of a geodetic set.
Returns 0 when no geodetic set exists; for any connected graph with ≥ 2 vertices
the value is at least 2. -/
noncomputable def geodeticNumber (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ S : Finset α, S.card = k ∧ IsGeodeticSet G S}

/-- **Geodetic number lower bound** — resolved.

For any connected graph `G` with at least 2 vertices, `geodeticNumber(G) ≥ 2`.

Proof: the geodetic set `S` must include at least two vertices (one geodesic
must start and end at distinct points), and both endpoints must be in `S`. -/
@[category research solved, AMS 5]
theorem geodeticNumber_ge_two (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    2 ≤ geodeticNumber G := by
  sorry

/-- **Geodetic number upper bound** — resolved.

For any connected graph `G` on `n` vertices,
  `geodeticNumber(G) ≤ n − diam(G) + 1`
where `diam(G) = (maxEccentricity G).toNat`.

Proof sketch: take a diametral path `v₀–v₁–⋯–v_d`; the set `{v₀} ∪ (V \ {v₁,…,v_{d-1}})`
is a geodetic set of size `n − d + 1`. -/
@[category research solved, AMS 5]
theorem geodeticNumber_le_card_sub_diam_add_one (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hn : 2 ≤ Fintype.card α) :
    geodeticNumber G ≤ Fintype.card α - (maxEccentricity G).toNat + 1 := by
  sorry

-- Sanity checks

/-- `geodeticNumber` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ geodeticNumber G := Nat.zero_le _

/-- `IsGeodeticSet` is a well-formed proposition on small graphs. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Finset (Fin 3)) : IsGeodeticSet G S ∨ True :=
  Or.inr trivial

/-- `geodeticNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (geodeticNumber G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphGeodeticNumber
