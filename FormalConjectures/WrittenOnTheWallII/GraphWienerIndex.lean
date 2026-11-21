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
# Wiener index bounds

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphWienerIndex

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- For a connected graph `G`, the Wiener index is at least `n · (n − 1) / 2`,
the value achieved by the complete graph `Kₙ` (all distances equal 1).
This is a sharp lower bound since `dist(u, v) ≥ 1` for all `u ≠ v` in a
connected graph. -/
@[category textbook, AMS 5]
theorem wienerIndex_lower_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    Fintype.card α * (Fintype.card α - 1) / 2 ≤ wienerIndex G := by
  sorry

/-- For a connected graph `G`, the Wiener index also satisfies
`wienerIndex(G) ≥ Fintype.card α * (Fintype.card α − 1) / 2 + G.indepNum − 1`.
This refines the trivial lower bound using the independence number. -/
@[category textbook, AMS 5]
theorem wienerIndex_indepNum_lower_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    Fintype.card α * (Fintype.card α - 1) / 2 + G.indepNum - 1 ≤ wienerIndex G := by
  sorry

-- Sanity checks

/-- The Wiener index of `K₃` is 3: pairs are (0,1), (0,2), (1,2), each at distance 1. -/
@[category test, AMS 5]
example : wienerIndex (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold wienerIndex
  sorry

/-- The Wiener index of the path `P₃` (0–1–2) is 4: dist(0,1)=1, dist(1,2)=1, dist(0,2)=2. -/
@[category test, AMS 5]
example : wienerIndex
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 4 := by
  unfold wienerIndex
  sorry

/-- The Wiener index of `K₄` is 6: all six pairs are at distance 1. -/
@[category test, AMS 5]
example : wienerIndex (⊤ : SimpleGraph (Fin 4)) = 6 := by
  unfold wienerIndex
  sorry

end WrittenOnTheWallII.GraphWienerIndex
