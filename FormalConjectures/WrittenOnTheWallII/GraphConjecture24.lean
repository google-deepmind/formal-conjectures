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

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture24

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `distEven G v` counts the number of vertices at even distance from `v` in `G`.
Distance 0 (the vertex itself) is even, so `distEven G v ≥ 1`. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Even (G.dist v w))).card

/--
WOWII [Conjecture 24](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`b(G) ≥ 2 · ⌈(1 + min_v distEven(v)) / 3⌉`
where `b(G)` is the largest induced bipartite subgraph size and
`distEven(v)` is the number of vertices at even distance from `v`.
-/
@[category research open, AMS 5]
theorem conjecture24 (G : SimpleGraph α) (h : G.Connected) :
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

end WrittenOnTheWallII.GraphConjecture24
