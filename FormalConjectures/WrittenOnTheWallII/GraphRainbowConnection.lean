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
# Rainbow Connection Number

*Reference:*
[G. Chartrand, G. L. Johns, K. A. McKeon, P. Zhang,
Rainbow connection in graphs, Math. Bohem. 133 (2008) 85–98](https://doi.org/10.21136/MB.2008.133947)

## Definition

An edge-coloring `c : E(G) → {1, …, k}` is **rainbow-connected** if for every
pair of distinct vertices `u, v` there exists a **rainbow path** from `u` to `v`
— a path all of whose edges receive distinct colors.

The **rainbow connection number** `rc(G)` is the minimum `k` for which such a
coloring exists.

We represent an edge-coloring as a map `c : Sym2 α → Fin k` (defined on all
unordered pairs; values on non-edges are ignored).

## Conjectures

1. (Resolved, trivial lower bound) `diam(G) ≤ rc(G)`.  A diametral path must be
   rainbow; hence its length (= `diam(G)`) bounds `rc(G)` from below.

2. (Resolved upper bound) For a connected graph `G` on `n ≥ 2` vertices,
   `rc(G) ≤ n - 1`.  Assigning distinct colors to the edges of any spanning tree
   gives a rainbow-connected coloring.
-/

namespace WrittenOnTheWallII.GraphRainbowConnection

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A `k`-edge-coloring `c : Sym2 α → Fin k` is **rainbow-connected** if for every
pair of distinct vertices there is a path (as a `Walk`) whose dart-colors are all
distinct (i.e., the list of colors along the path has no duplicates). -/
def IsRainbowConnected (G : SimpleGraph α) {k : ℕ} (c : Sym2 α → Fin k) : Prop :=
  ∀ u v : α, u ≠ v →
    ∃ p : G.Walk u v, p.IsPath ∧
      List.Nodup (p.darts.map (fun d => c (Sym2.mk d.toProd)))

/-- The **rainbow connection number** `rc(G)`: the minimum number of colors in a
rainbow-connected edge-coloring.  The value `sInf ∅ = 0` in Lean's `sInf`
convention is harmless for disconnected or trivial graphs. -/
noncomputable def rainbowConnectionNumber (G : SimpleGraph α) : ℕ :=
  sInf {k | ∃ c : Sym2 α → Fin k, IsRainbowConnected G c}

/-- **Diameter lower bound** (resolved): `diam(G) ≤ rc(G)`.

Proof sketch: any rainbow path between two vertices at distance `diam(G)` must
have at least `diam(G)` edges, and each must have a distinct color, so at least
`diam(G)` colors are needed. -/
@[category research solved, AMS 5]
theorem diameter_le_rainbowConnectionNumber
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) :
    G.diam ≤ rainbowConnectionNumber G := by
  sorry

/-- **Upper bound** (resolved): for a connected graph `G` on `n` vertices,
`rc(G) ≤ n - 1`.

Proof sketch: color the edges of any spanning tree with `n - 1` distinct colors
and assign an arbitrary color to each non-tree edge; the spanning tree provides a
rainbow path between any two vertices. -/
@[category research solved, AMS 5]
theorem rainbowConnectionNumber_le_card_sub_one
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 2 ≤ Fintype.card α) :
    rainbowConnectionNumber G ≤ Fintype.card α - 1 := by
  sorry

-- Sanity checks

/-- `rainbowConnectionNumber` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ rainbowConnectionNumber G :=
  Nat.zero_le _

/-- `IsRainbowConnected` is a well-formed proposition on small graphs. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (c : Sym2 (Fin 3) → Fin 2) :
    IsRainbowConnected G c ∨ True :=
  Or.inr trivial

/-- `rainbowConnectionNumber` cast to `ℝ` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : (0 : ℝ) ≤ (rainbowConnectionNumber G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphRainbowConnection
