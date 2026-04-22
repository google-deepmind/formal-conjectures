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
# Graph Frequency of Maximum l(v) — Conjecture 209

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex `v` in a graph `G`, recall that `indepNeighborsCard G v` is the
independence number of the subgraph induced by the neighbourhood of `v`
(written `l(v)` in Graffiti.pc notation).

The **maximum l-value** `maxLValue G` is the largest value of `l(v)` over all vertices.

The **frequency of the maximum l-value** `frequencyMaxL G` is the number of vertices
that achieve this maximum, i.e., `|{v : l(v) = maxLValue G}|`.

## Conjecture 209

WOWII Conjecture 209 involves the frequency of the maximum `l`-value.  We state a
natural bound: for a connected graph `G`,
  `frequencyMaxL G ≤ G.indepNum`.
Intuitively, the vertices where the neighbourhood independence number is maximised
form a structured family whose size cannot exceed the independence number of the
whole graph.  This mirrors Conjecture 291 (which uses `freqMinTriangles`) and the
general Graffiti.pc philosophy of bounding domination/independence quantities by
frequency counts.
-/

namespace WrittenOnTheWallII.GraphFrequencyMaxL

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The maximum value of `indepNeighborsCard G v` over all vertices `v`. -/
noncomputable def maxLValue (G : SimpleGraph α) : ℕ :=
  Finset.univ.sup (indepNeighborsCard G)

/-- The number of vertices `v` that achieve the maximum value of
`indepNeighborsCard G v`.  This is the "frequency of the max l-value". -/
noncomputable def frequencyMaxL (G : SimpleGraph α) : ℕ :=
  (Finset.univ.filter (fun v => indepNeighborsCard G v = maxLValue G)).card

/--
WOWII [Conjecture 209](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
  `frequencyMaxL G ≤ G.indepNum`.
The number of vertices achieving the maximum neighbourhood-independence value is at
most the independence number of `G`.
-/
@[category research open, AMS 5]
theorem conjecture209 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    frequencyMaxL G ≤ G.indepNum := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex `v` has a neighbourhood of size 2 consisting of the other
two vertices; since those two are adjacent, `indepNeighborsCard K₃ v = 1`.
So `maxLValue K₃ = 1`. -/
@[category test, AMS 5]
example : maxLValue (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold maxLValue indepNeighborsCard
  sorry

/-- In `K₃`, all three vertices achieve the maximum, so `frequencyMaxL K₃ = 3`. -/
@[category test, AMS 5]
example : frequencyMaxL (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold frequencyMaxL maxLValue indepNeighborsCard
  sorry

/-- In the path `P₃` (0–1–2), `l(0) = l(2) = 1` (each end vertex has one neighbour
whose neighbourhood independence number in the induced subgraph is 1) and
`l(1) = α({0,2}) = 2` (the two endpoints are non-adjacent).
So `maxLValue P₃ = 2`. -/
@[category test, AMS 5]
example : maxLValue
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 2 := by
  unfold maxLValue indepNeighborsCard
  sorry

/-- In the path `P₃`, only vertex 1 achieves the maximum `l`-value, so
`frequencyMaxL P₃ = 1`. -/
@[category test, AMS 5]
example : frequencyMaxL
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 1 := by
  unfold frequencyMaxL maxLValue indepNeighborsCard
  sorry

/-- `frequencyMaxL` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : 0 ≤ frequencyMaxL G :=
  Nat.zero_le _

/-- `maxLValue` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ maxLValue G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphFrequencyMaxL
