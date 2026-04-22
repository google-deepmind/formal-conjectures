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
# Written on the Wall II - Conjecture 84

**Verbatim statement (WOWII #84, status O):**
> If G is a simple connected graph, then tree(G) ≥ 2rad(G)/δ(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj84


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture84

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/--
WOWII [Conjecture 84](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`tree(G) ≥ 2 · rad(G) / d(G)`
where `tree(G)` is the number of vertices in a largest induced tree,
`rad(G) = G.radius` is the radius (minimum eccentricity) of `G`, and
`d(G) = averageDistance G` is the average distance between pairs of vertices.
-/
@[category research open, AMS 5]
theorem conjecture84 (G : SimpleGraph α) (h : G.Connected) (hd : 0 < averageDistance G) :
    2 * G.radius.toNat / averageDistance G ≤ (largestInducedTreeSize G : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The largest induced tree size is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (largestInducedTreeSize G : ℝ) :=
  Nat.cast_nonneg _

end WrittenOnTheWallII.GraphConjecture84
