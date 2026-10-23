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
# Written on the Wall II - Conjecture 19

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section



namespace WrittenOnTheWallII.GraphConjecture19

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 19](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is connected then the size `b(G)` of a largest induced bipartite subgraph
satisfies
`b(G) ≥ FLOOR((∑ ecc(v))/(|V|) + sSup (range (l G)))`, where `ecc(v)` denotes
eccentricity and `l(G)` is the independence number of neighbourhoods.

**Proof outline.** Pick `u` maximising `l(u)`, let `e = ecc(u)` and `D = diam(G)`, and let
`I ⊆ N(u)` be an independent set with `|I| = l(u)`. Any family of sets `B d`, each
independent and contained in the distance sphere `{v | dist(u, v) = d}`, induces a bipartite
subgraph (colour by the parity of `dist(u, ·)`), so `b(G) ≥ ∑ |B d|`.
* If `D ≤ e`, every eccentricity is at most `e`, so the average is at most `e`. Take
  `B 0 = {u}`, `B 1 = I`, and one vertex of a geodesic from `u` to an eccentric vertex on
  each sphere `2 ≤ d ≤ e`; this gives `b(G) ≥ e + l(u)`.
* If `e < D`, the average eccentricity is strictly less than `D`. Take a diametral pair
  `x, y`. On each sphere `d` in a suitable range, the vertices of geodesics `u → x` and
  `u → y` at distance `d` from `u` are at distance at least `2` from each other (triangle
  inequality with `dist(x, y) = D`), so they can share `B d`; counting gives
  `b(G) ≥ D - 1 + l(u)`.
In both cases the floor of the average plus `l(u)` is at most `b(G)`.
-/
@[category research solved, AMS 5,
  formal_proof using lean4 at
    "https://github.com/hamsade-google/formal-conjectures/blob/a94666dbdeef42d593a6c1aecf388c396db7c3fb/FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean"]
theorem conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  sorry

end WrittenOnTheWallII.GraphConjecture19
