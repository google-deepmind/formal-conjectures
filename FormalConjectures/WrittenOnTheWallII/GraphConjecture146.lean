/-
Copyright 2026 The Formal Conjectures Authors.

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
# Written on the Wall II - Conjecture 146

**Verbatim statement (WOWII #146, status O):**
> If G is a simple connected graph, then tree(G) ≥ 2*ecc(B)/rad(G^2)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj146


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **square** of a graph `G`, denoted `G²`, is the graph on the same vertex set where
two distinct vertices are adjacent if and only if their distance in `G` is at most 2.

The **radius of G²** is the minimum eccentricity of any vertex in `G²`, i.e.,
  `rad(G²) = min_{v ∈ V} max_{u ∈ V} dist_{G²}(u, v)`.
-/

namespace WrittenOnTheWallII.GraphConjecture146

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The radius of `G²` (the graph square): the minimum eccentricity over all vertices
of `graphSquare G`. The base graph operation `graphSquare` is from
`FormalConjecturesForMathlib`. -/
noncomputable def graphSquareRadius (G : SimpleGraph α) : ℕ :=
  (minEccentricity (graphSquare G)).toNat

/--
WOWII [Conjecture 146](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`tree(G) ≥ 2 * ecc(B) / rad(G²)`
where `tree(G)` is the number of vertices in a largest induced subtree,
`ecc(B)` is the eccentricity of the boundary vertices of `G` (`eccSet` and
`boundaryVertices` from `FormalConjecturesForMathlib`), and
`rad(G²)` is the radius of the square graph of `G`.

We state the inequality in the form `tree(G) * rad(G²) ≥ 2 * ecc(B)` to avoid division.
-/
@[category research open, AMS 5]
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (boundaryVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G := by
  sorry

-- Sanity checks

/-- In `graphSquare G`, adjacent vertices in `G` are also adjacent (dist ≤ 1 ≤ 2). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (u v : Fin 4) (h : G.Adj u v) :
    (graphSquare G).Adj u v := by
  refine ⟨G.ne_of_adj h, ?_⟩
  -- dist u v ≤ length of the 1-step walk ≤ 2
  exact (G.dist_le (Walk.cons h Walk.nil)).trans (by norm_num)

/-- `graphSquare` is loopless: no vertex is adjacent to itself. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : ¬(graphSquare G).Adj v v := by
  simp [graphSquare]

/-- The `graphSquareRadius` is nonneg for any graph. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ graphSquareRadius G := Nat.zero_le _

/-- `graphSquare G` adjacency is symmetric. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (u v : Fin 4) (h : (graphSquare G).Adj u v) :
    (graphSquare G).Adj v u :=
  (graphSquare G).symm h

end WrittenOnTheWallII.GraphConjecture146
