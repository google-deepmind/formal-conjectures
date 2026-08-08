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

import FormalConjecturesUtil

/-!
# distOdd Invariant and WOWII Conjecture

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a vertex `v` in a graph `G`, define:
- `distEven G v`: number of vertices at **even** distance from `v` (including `v` itself
  at distance 0).
- `distOdd G v`: number of vertices at **odd** distance from `v`.

These two quantities partition the vertex set: `distEven G v + distOdd G v = n`.

## Conjecture

This file states a Graffiti.pc-style upper bound using the minimum of
`distOdd`:

`α(G) ≤ 1 + min_v distOdd(v) · (max_v l(v) - 1)`

where `α(G) = G.indepNum` is the independence number and `l(v) = indepNeighborsCard G v`.

**Not a verbatim WOWII transcription.** This is the `distOdd`-analogue of
WOWII Conjecture 96 (which uses `distEven`); we file it as a new
Graffiti.pc-style observation rather than a formalisation of any specific
numbered WOWII conjecture.

For bipartite graphs, one of the two parts has all vertices at even (resp. odd) distance
from any fixed vertex in one part; so `distOdd` tracks the "opposite part" size.
-/

namespace WrittenOnTheWallII.GraphDistOdd

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- For any vertex `v`, the number of vertices at even distance from `v`
(including `v` itself, at distance 0) plus `distOdd G v` equals the total number
of vertices: every vertex is at either even or odd distance from `v`. -/
@[category research solved, AMS 5]
theorem card_even_dist_add_distOdd (G : SimpleGraph α) (v : α) :
    (Finset.univ.filter (fun w => Even (G.dist v w))).card + distOdd G v =
      Fintype.card α := by
  unfold distOdd
  rw [← Finset.card_union_of_disjoint]
  · rw [← Finset.filter_or]
    congr 1
    ext w; simp
    exact (Nat.even_or_odd (G.dist v w)).imp id id
  · apply Finset.disjoint_filter.mpr
    intro w _ he ho
    exact (Nat.not_odd_iff_even.mpr he) ho

/--
**distOdd upper bound for the independence number** (WOWII-style conjecture).

For a simple connected graph `G`,
`α(G) ≤ 1 + min_v distOdd(v) · (max_v l(v) - 1)`
where `α(G) = G.indepNum` is the independence number,
`distOdd(v)` is the number of vertices at odd distance from `v`, and
`max_v l(v)` is the maximum independence number of a vertex neighbourhood.

This is the odd-distance analogue of WOWII Conjecture 96.
-/
@[category research open, AMS 5]
theorem distOdd_indepNum_upper_bound [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    let minDistOdd := (Finset.univ.image (distOdd G)).min' (by simp)
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistOdd : ℝ) * ((maxL : ℝ) - 1) := by
  sorry

-- Sanity checks

/-- `distOdd G v` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 ≤ distOdd G v := Nat.zero_le _

/-- `distOdd K₃ 0 = 2`: from vertex 0 in `K₃`, both vertices 1 and 2 are at distance 1
(odd). -/
@[category test, AMS 5]
example : distOdd (⊤ : SimpleGraph (Fin 3)) 0 = 2 := by
  unfold distOdd
  sorry

/-- `distOdd` never exceeds the number of vertices. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : distOdd G v ≤ 3 := by
  have := card_even_dist_add_distOdd G v
  simp only [Fintype.card_fin] at this
  omega

end WrittenOnTheWallII.GraphDistOdd
