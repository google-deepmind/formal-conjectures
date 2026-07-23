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
# Graph Degree Mode Invariants

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a graph `G`, the **degree count** `degreeCount G d` is the number of vertices
having degree exactly `d`.  The **maximum degree count** `maxDegreeCount G` is the
frequency of the most common degree value (the mode frequency).  The
**mode-min degree** `modeDegreeMin G` is the smallest degree value that attains this
maximum frequency; it is the minimum element of the set of modal degree values.

## Conjecture

For a connected graph `G` with at least 2 vertices, `modeDegreeMin G ≥ 1`.
Intuitively, in any connected graph every vertex has at least one neighbour, so
the degree-0 class is empty and the modal degree value must be positive.
-/

namespace WrittenOnTheWallII.GraphMode

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The number of vertices of `G` whose degree equals `d`. -/
noncomputable def degreeCount (G : SimpleGraph α) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = d)).card

/-- The maximum over all degrees `d` of `degreeCount G d`.
This is the frequency of the most-common degree value (mode frequency). -/
noncomputable def maxDegreeCount (G : SimpleGraph α) : ℕ :=
  (Finset.range (Fintype.card α + 1)).sup (degreeCount G)

/-- The smallest degree value achieving the mode frequency.
This is defined via `sInf` on the (nonempty when the graph has vertices) set of
modal degrees.  When the graph has no vertices this set may be empty; the
`sInf ℕ` convention then yields 0. -/
noncomputable def modeDegreeMin (G : SimpleGraph α) : ℕ :=
  sInf {d | degreeCount G d = maxDegreeCount G}

/--
WOWII-style conjecture: For a simple connected graph `G` with at least 2 vertices,
the minimum modal degree satisfies `modeDegreeMin G ≥ 1`.

In a connected graph every vertex has degree ≥ 1, so `degreeCount G 0 = 0`.
Because some vertex has degree ≥ 1, there exists `d ≥ 1` with
`degreeCount G d > 0 = degreeCount G 0`.  Hence the modal degree value must be ≥ 1.
-/
@[category research open, AMS 5]
theorem modeDegreeMin_pos (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    1 ≤ modeDegreeMin G := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex has degree 2.  So `degreeCount K₃ 2 = 3`. -/
@[category test, AMS 5]
example : degreeCount (⊤ : SimpleGraph (Fin 3)) 2 = 3 := by
  unfold degreeCount
  sorry

/-- In `K₃`, the only non-zero degree count is at `d = 2`, so `maxDegreeCount K₃ = 3`. -/
@[category test, AMS 5]
example : maxDegreeCount (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold maxDegreeCount degreeCount
  sorry

/-- In `K₃`, the modal degree (minimum mode value) is 2. -/
@[category test, AMS 5]
example : modeDegreeMin (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold modeDegreeMin maxDegreeCount degreeCount
  sorry

/-- In the path `P₄` (0–1–2–3), degrees are 1,2,2,1.  So the mode is 2 and
`modeDegreeMin P₄ = 2`. -/
@[category test, AMS 5]
example : modeDegreeMin
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3)} : SimpleGraph (Fin 4)) = 2 := by
  unfold modeDegreeMin maxDegreeCount degreeCount
  sorry

/-- `modeDegreeMin` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : 0 ≤ modeDegreeMin G :=
  Nat.zero_le _

/-- `maxDegreeCount` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ maxDegreeCount G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphMode
