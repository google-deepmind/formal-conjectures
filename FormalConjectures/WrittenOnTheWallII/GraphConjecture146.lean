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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 146

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **square** of a graph $G$, denoted $G^2$, is the graph on the same vertex set
where two distinct vertices are adjacent if and only if their distance in $G$ is at
most $2$.

The **radius of $G^2$** is the minimum eccentricity of any vertex in $G^2$, i.e.,
$$\mathrm{rad}(G^2) = \min_{v \in V} \max_{u \in V} \mathrm{dist}_{G^2}(u, v).$$
-/

namespace WrittenOnTheWallII.GraphConjecture146

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The radius of $G^2$ (the graph square): the minimum eccentricity over all vertices
of `graphSquare G`. -/
noncomputable def graphSquareRadius (G : SimpleGraph α) : ℕ :=
  (graphSquare G).radius.toNat

/--
WOWII [Conjecture 146](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph $G$,
$\mathrm{tree}(G) \ge 2 \cdot \mathrm{ecc}(B) / \mathrm{rad}(G^2)$
where $\mathrm{tree}(G)$ is the number of vertices in a largest induced subtree,
$\mathrm{ecc}(B)$ is the eccentricity of the boundary vertices of $G$ (`eccSet`
and `maxEccentricityVertices`), and $\mathrm{rad}(G^2)$ is the radius of the square
graph of $G$.

We state the inequality in the form
$\mathrm{tree}(G) \cdot \mathrm{rad}(G^2) \ge 2 \cdot \mathrm{ecc}(B)$ to avoid division.

## Informal proof

Write $t$ for the largest induced-tree order, $r$ and $d$ for the radius and
diameter of $G$, and $p$ for the eccentricity of its peripheral set.  First,
the distance in the graph square is
$\operatorname{dist}_{G^2}(u,v)=\lceil\operatorname{dist}_G(u,v)/2\rceil$,
so $\operatorname{rad}(G^2)=\lceil r/2\rceil$.  A diametral geodesic is an
induced path, giving $t\ge d+1$, while $p\le d-1$.  These bounds settle every
case except $r=2$, $d=4$, and $p=3$.  In that remaining configuration, choose
a centre and shortest paths to two diametral vertices and to a vertex at
distance three from the peripheral set.  A finite case analysis on the two
possible cross-arm edges (and then the possible chords) always produces an
induced tree on at least six vertices.  Hence $t\,\operatorname{rad}(G^2)
\ge 2p$ in the exceptional case as well.
-/
@[category research solved, AMS 5, formal_proof using lean4 at "https://github.com/akakabrian/WOW-146/blob/f9e0ad75d829170804ce1d8f9fd4c1d4a0085203/WOW146/Conjecture146.lean"]
theorem conjecture146 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hrad : 0 < graphSquareRadius G) :
    2 * eccSet G (maxEccentricityVertices G : Set α) ≤
    largestInducedTreeSize G * graphSquareRadius G := by
  sorry

-- Sanity checks

/-- In `graphSquare G`, adjacent vertices in $G$ are also adjacent
($\mathrm{dist} \le 1 \le 2$). -/
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
