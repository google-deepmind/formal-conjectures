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
# Written on the Wall II - Conjecture 63

**Verbatim statement (WOWII #63, status O):**
> If G is a simple connected graph, then f(G) ≥ CEIL[(minimum of dist_even(v) + b(G) + 1)/3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj63


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture63

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 63](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`f(G) ≥ ⌈(min_v distEven(v) + b(G) + 1) / 3⌉`
where `f(G) = largestInducedForestSize G` is the size of a largest induced forest,
`b(G)` is the largest induced bipartite subgraph size, and
`distEven(v)` is the number of vertices at even distance from `v`.
-/
@[category research open, AMS 5]
theorem conjecture63 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    ⌈((minDistEven : ℝ) + b G + 1) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The largest induced forest size is a natural number (nonneg). -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- `distEven` of any vertex is positive. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 < distEven G v := by
  unfold distEven
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, by simp [SimpleGraph.dist_self]⟩⟩⟩

end WrittenOnTheWallII.GraphConjecture63
