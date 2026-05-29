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
# Written on the Wall II - Conjecture 25

**Verbatim statement (WOWII #25, status F):**
> If G is a simple connected graph, then b(G) ≥ 2 CEIL[(1 + minimum of dist_even(v))/3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj25

This conjecture is **disproved** on the WOWII page (status F; "same
counterexample as in #24"). Following the upstream pattern established in
#3823 for Conjecture 23, we record the disproof using `answer(False) ↔ ...`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture25

open Classical SimpleGraph

/--
WOWII [Conjecture 25](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj25)
(status F, disproved):

For every finite simple connected graph `G`,
`b(G) ≥ 2 · ⌈(1 + min_v dist_even(v)) / 3⌉`
where `b(G)` is the size of a largest induced bipartite subgraph and
`dist_even(v)` is the number of vertices at even distance from `v`.
-/
@[category research solved, AMS 5]
theorem conjecture25 : answer(False) ↔
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
        2 * ⌈(1 + (minDistEven : ℝ)) / 3⌉ ≤ b G := by
  sorry

-- Sanity checks

/-- `distEven G v` is always at least 1, since `v` itself is at distance 0 (even) from itself. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) (v : Fin 4) : 1 ≤ distEven G v := by
  unfold distEven
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, by simp [SimpleGraph.dist_self]⟩⟩⟩

/-- The invariant `b G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture25
