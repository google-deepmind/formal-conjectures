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
# Written on the Wall II - Conjecture 91

**Verbatim statement (WOWII #91, status O):**
> If G is a simple connected graph, then b(G) ≤ 1 + f(G) * (CEIL[average of λ(v) ])/2

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj91

This conjecture is **false**: Max Talwar found an 11-vertex counterexample
(graph6 `JBza_CB?wF_`): take `K₃,₃` minus an edge together with a `K₅`, joined
by two bridges into one `K₅`-vertex. There the average neighbourhood
independence number is exactly `2`, the largest induced forest has `6` vertices,
and the largest induced bipartite subgraph has `8`, so the conjectured bound
reads `8 ≤ 1 + 6·⌈2⌉/2 = 7`. We therefore record the statement as disproved,
using the `answer(False) ↔ ...` pattern of Conjectures 23/24/25.

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [Counterexample certificate for WOWII 91 (Max Talwar)](https://github.com/maxtalwar/wowii91-counterexample/releases/tag/v1.0.0)
-/

namespace WrittenOnTheWallII.GraphConjecture91

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 91](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
(disproved, 2026):

For a simple connected graph `G`,
`b(G) ≤ 1 + f(G) · ⌈avg_v l(v)⌉ / 2`
where `b(G)` is the largest induced bipartite subgraph size,
`f(G) = largestInducedForestSize G` is the largest induced forest size, and
`avg_v l(v) = l G` is the average independence number of the neighbourhoods.

Disproved by an 11-vertex counterexample (Max Talwar, 2026; graph6
`JBza_CB?wF_`) with `b(G) = 8`, `f(G) = 6` and `l G = 2`, violating
`8 ≤ 1 + 6·⌈2⌉/2 = 7`.
-/
@[category research solved, AMS 5]
theorem conjecture91 : answer(False) ↔
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        b G ≤ 1 + (G.largestInducedForestSize : ℝ) * ⌈l G⌉ / 2 := by
  sorry

-- Sanity checks

/-- The invariant `b G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

/-- The average indep-neighbors `l G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ l G := by
  unfold l averageIndepNeighbors
  apply div_nonneg
  · apply Finset.sum_nonneg; intro v _; exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture91
