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
# Written on the Wall II - Conjecture 18

**Verbatim statement (WOWII #18, status T):**
> If G is a simple connected graph, then b(G) ≥ α(G) + CEIL(sqrt(dist_max(M)))

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj18


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture18

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 18](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, the size `b(G)` of a largest induced bipartite subgraph
satisfies `b(G) ≥ α(G) + ⌈√(eccSet(G, M))⌉`, where `α(G)` is the independence number,
`M` is the set of maximum-degree vertices, and `eccSet(G, M)` is the set eccentricity
of `M` — the maximum over all vertices of the minimum distance from that vertex to `M`.
We use the upstream `SimpleGraph.eccSet` invariant from
`FormalConjecturesForMathlib/.../Invariants.lean`.
-/
@[category research solved, AMS 5]
theorem conjecture18 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let M : Set α := {v | G.degree v = G.maxDegree}
    (G.indepNum : ℝ) + ⌈Real.sqrt (eccSet G M : ℝ)⌉ ≤ b G := by
  sorry

-- Sanity checks

/-- The invariant `b G` is nonneg (cast of a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- In `K₃`, the max degree is 2. -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).maxDegree = 2 := by decide +native

/-- `eccSet G S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Set (Fin 3)) : 0 ≤ eccSet G S := Nat.zero_le _

/-- `distToSet G v S` is always nonneg (it is a natural number). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) : 0 ≤ distToSet G v S :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture18
