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
# Written on the Wall II - Conjecture 19

**Verbatim statement (WOWII #19, status O):**
> If G is a simple connected graph, then b(G) ≥ FLOOR(average of ecc(v) + maximum of λ(v))

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj19

Here `b(G)` is the **size of a largest induced bipartite subgraph** of `G`
(see `FormalConjecturesForMathlib.Combinatorics.SimpleGraph.GraphConjectures.Definitions`,
where `b` is defined). It is **not** the independence number.

The DeLaVina note on the WOWII page (June 22, 2005) observes that if
`average of ecc(v) ≤ diam − 1`, this conjecture follows from Conjecture 13.

The auxiliary `graphLength G = ∑_v ecc(v)` (`length(G)` in DeLaVina's
notation) is retained below because `length(G)/n = averageEccentricity G`,
and some neighbouring Graffiti.pc-style observations use the unscaled
`length(G)` directly.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphLength

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **length** of `G` in DeLaVina's WOWII notation: the sum of
eccentricities over all vertices. We have
`graphLength G / Fintype.card α = averageEccentricity G`. -/
noncomputable def graphLength (G : SimpleGraph α) : ℕ :=
  ∑ v : α, (eccentricity G v).toNat

/--
WOWII [Conjecture 19](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj19)
(status O):

For a simple connected graph `G`,
`b(G) ≥ ⌊avg_v ecc(v) + max_v l(v)⌋`,
where `b(G)` is the size of a largest induced bipartite subgraph,
`ecc(v)` is the eccentricity of `v` (so `avg_v ecc(v) = averageEccentricity G`),
and `l(v) = indepNeighborsCard G v` is the independence number of the
neighbourhood of `v`.
-/
@[category research open, AMS 5]
theorem conjecture19 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (⌊averageEccentricity G + (maxL : ℝ)⌋ : ℝ) ≤ b G := by
  sorry

-- Sanity checks

/-- `graphLength` is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ graphLength G := Nat.zero_le _

/-- `graphLength` of any graph is nonneg as a real. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : (0 : ℝ) ≤ (graphLength G : ℝ) :=
  Nat.cast_nonneg _

/-- `b G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

end WrittenOnTheWallII.GraphLength
