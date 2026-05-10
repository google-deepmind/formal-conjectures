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
import FormalConjectures.WrittenOnTheWallII.GraphConjecture133

/-!
# Written on the Wall II - Conjecture 160

**Verbatim statement (WOWII #160, status O):**
> If G is a simple connected graph, then L_s(G) ≥ maximum of l(v) + maximum T(v)*χ_C4(G).

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj160


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex `v` in `G`, **T(v)** is the number of triangles incident to `v`:
  `T(v) = |{u, w} ⊆ N(v) | u ~ w|`
i.e., the number of pairs of neighbors of `v` that are themselves adjacent.

The invariant `maxTrianglesAtVertex G` is the maximum of T(v) over all vertices.

**Conjecture 160** uses both `max T(v)` and `c_C4(G)` (the number of induced 4-cycles,
already defined in GraphConjecture133) to lower bound the WOWII invariant `L_s(G)`,
which is the **maximum number of leaves over all spanning trees of `G`** (exposed
in our library as `SimpleGraph.Ls G : ℝ` in
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/GraphConjectures/Definitions.lean`).
-/

namespace WrittenOnTheWallII.GraphConjecture160

open Classical SimpleGraph WrittenOnTheWallII.GraphConjecture133

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The number of triangles incident to vertex `v`: the number of 3-cliques containing `v`.
A 3-clique containing `v` corresponds to a pair of neighbors of `v` that are adjacent. -/
noncomputable def numTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] (v : α) : ℕ :=
  ((G.cliqueFinset 3).filter (fun s => v ∈ s)).card

/-- The maximum number of triangles incident to any vertex in `G`. -/
noncomputable def maxTrianglesAtVertex (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.image (numTrianglesAtVertex G)).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/--
WOWII [Conjecture 160](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`L_s(G) ≥ max_v l(v) + max_v T(v) * c_C4(G)`
where:
- `L_s(G) = SimpleGraph.Ls G` is the maximum number of leaves over all spanning
  trees of `G`,
- `max_v l(v)` is the maximum local independence number over vertices,
- `max_v T(v)` is the maximum number of triangles incident to any vertex,
- `c_C4(G)` is the number of induced 4-cycles in `G`.
-/
@[category research open, AMS 5]
theorem conjecture160 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    let maxT := maxTrianglesAtVertex G
    let cC4 := countInducedC4 G
    (maxL : ℝ) + (maxT : ℝ) * (cC4 : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex has 1 triangle incident to it. -/
@[category test, AMS 5]
example : numTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) (0 : Fin 3) = 1 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In `K₃`, `maxTrianglesAtVertex = 1`. -/
@[category test, AMS 5]
example : maxTrianglesAtVertex (⊤ : SimpleGraph (Fin 3)) = 1 := by
  unfold maxTrianglesAtVertex numTrianglesAtVertex
  decide +native

/-- In the path `P₃`, vertex 1 is adjacent to 0 and 2, but 0 and 2 are not adjacent.
So `T(1) = 0`. -/
@[category test, AMS 5]
example : numTrianglesAtVertex
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) (1 : Fin 3) = 0 := by
  unfold numTrianglesAtVertex
  decide +native

/-- In `K₃`, `countInducedC4 = 0` (no induced 4-cycles in a 3-vertex graph). -/
@[category test, AMS 5]
example : countInducedC4 (⊤ : SimpleGraph (Fin 3)) = 0 := by
  unfold countInducedC4 isInducedC4
  decide +native

end WrittenOnTheWallII.GraphConjecture160
