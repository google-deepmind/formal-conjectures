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
import FormalConjectures.WrittenOnTheWallII.GraphMode

/-!
# Graph Even Mode-Min Count Invariant

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition

Recall that `modeDegreeMin G` (from `GraphMode.lean`) is the smallest degree
value that achieves the mode frequency in the degree sequence of `G`.

The **even mode-min count** `evenModeMinCount G` is the number of vertices `v`
whose degree is equal to `modeDegreeMin G` **and** whose degree is even.  In
other words, it counts vertices at the minimum modal degree if and only if that
degree value is even (otherwise the count is 0).

## Conjecture

WOWII-style conjecture: For a simple connected graph `G`,
`G.indepNum ≤ evenModeMinCount G * (Finset.univ.sup (indepNeighborsCard G)) + 1`.

The right-hand side bounds the independence number by the product of the
"even-parity mode-frequency" and the maximum neighbourhood independence value,
plus 1.  This mirrors the Graffiti.pc philosophy of combining frequency
statistics with neighbourhood invariants.
-/

namespace WrittenOnTheWallII.GraphEvenModeMin

open Classical SimpleGraph WrittenOnTheWallII.GraphMode

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The number of vertices whose degree equals `modeDegreeMin G` **and** is even.
When `modeDegreeMin G` is odd, every vertex counted by `modeDegreeMin G` has an
odd degree, so `evenModeMinCount G = 0`. -/
noncomputable def evenModeMinCount (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = modeDegreeMin G ∧ Even (G.degree v))).card

/--
**WOWII-style open conjecture**: For a simple connected graph `G`,
`G.indepNum ≤ evenModeMinCount G * (Finset.univ.sup (indepNeighborsCard G)) + 1`.

The independence number is bounded above by the product of the number of vertices
at the minimum modal degree (even-degree variant) and the maximum neighbourhood
independence number, plus 1.  The `+1` accounts for the case where
`evenModeMinCount G = 0` (all vertices at the minimum modal degree have odd
degree), in which case the bound trivially becomes `G.indepNum ≤ 1`.
-/
@[category research open, AMS 5]
theorem evenModeMinCount_indepNum_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    G.indepNum ≤ evenModeMinCount G * Finset.univ.sup (indepNeighborsCard G) + 1 := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex has degree 2 (even), `modeDegreeMin K₃ = 2`, so all
3 vertices qualify; `evenModeMinCount K₃ = 3`. -/
@[category test, AMS 5]
example : evenModeMinCount (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold evenModeMinCount modeDegreeMin maxDegreeCount degreeCount
  sorry

/-- In the path `P₃` (0–1–2), degrees are `[1, 2, 1]`.  `modeDegreeMin P₃ = 1`
(degree 1 appears twice, degree 2 appears once).  Degree 1 is odd, so no vertex
qualifies; `evenModeMinCount P₃ = 0`. -/
@[category test, AMS 5]
example : evenModeMinCount
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 0 := by
  unfold evenModeMinCount modeDegreeMin maxDegreeCount degreeCount
  sorry

/-- `evenModeMinCount` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ evenModeMinCount G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphEvenModeMin
