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
# Written on the Wall II - Conjecture 24

**Verbatim statement (WOWII #24, status F):**
> If G is a simple connected graph, then b(G) ≥ λ(G) + CEIL[minimum of dist_even(v)/3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj24

This conjecture is **disproved** on the WOWII page (status F). Following the
upstream pattern established in #3823 for the closely related Conjecture 23,
we record the disproof using `answer(False) ↔ ...`.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture24

open Classical SimpleGraph

/-- `distEven G v` counts the number of vertices at even distance from `v` in `G`.
Distance 0 (the vertex itself) is even, so `distEven G v ≥ 1`. -/
noncomputable def distEven {α : Type*} [Fintype α]
    (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Even (G.dist v w))).card

/--
WOWII [Conjecture 24](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj24)
(status F, disproved):

For every finite simple connected graph `G`,
`b(G) ≥ λ(G) + ⌈(min_v dist_even(v)) / 3⌉`
where `b(G)` is the size of a largest induced bipartite subgraph,
`λ(G) := max_v l(v)` is the maximum over all vertices of the independence
number of the open neighbourhood of `v`, and `dist_even(v)` is the number of
vertices at even distance from `v`.
-/
@[category research solved, AMS 5]
theorem conjecture24 : answer(False) ↔
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
        let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
        (maxL : ℝ) + ⌈(minDistEven : ℝ) / 3⌉ ≤ b G := by
  sorry

-- Sanity checks

/-- `distEven G v` is always positive, since `v` itself is at distance 0 (even) from itself. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 < distEven G v := by
  unfold distEven
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨0, by simp [SimpleGraph.dist_self]⟩⟩⟩

/-- The invariant `b G` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture24
