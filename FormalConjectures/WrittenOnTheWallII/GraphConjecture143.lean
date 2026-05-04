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
# Written on the Wall II - Conjecture 143

**Verbatim statement (WOWII #143, status O):**
> If G is a simple connected graph, then tree(G) ≥ (girth + 1)/σ(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj143


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture143

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `largestInducedTreeSize G` is the number of vertices in a largest induced subtree of `G`. -/
noncomputable def largestInducedTreeSize (G : SimpleGraph α) : ℕ :=
  sSup { n | ∃ s : Finset α, s.card = n ∧ (G.induce (s : Set α)).IsTree }

/-- The **2-domination number** of `G` (Fink–Jacobson 1985): the minimum size
of a set `S` such that every vertex outside `S` has at least 2 neighbours in `S`.

This is DeLaVina's `σ(G)`, used consistently across WOWII conjectures
143, 188, 189, 190, and 201. -/
noncomputable def twoDominationNumber (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sInf { n | ∃ S : Finset α, S.card = n ∧
    ∀ v ∉ S, 2 ≤ (S.filter (fun w => G.Adj v w)).card }

/--
WOWII [Conjecture 143](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`tree(G) ≥ (girth(G) + 1) / σ(G)`
where `tree(G)` is the largest induced tree size, `girth(G)` is the length of
the shortest cycle, and `σ(G) = twoDominationNumber G` is the 2-domination
number of `G`.  We use real-number division; when `σ(G) = 0` the right-hand
side is interpreted as `+∞`, which is vacuously true.
-/
@[category research open, AMS 5]
theorem conjecture143 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hσ : 0 < twoDominationNumber G) :
    (G.girth : ℝ) + 1 ≤ (largestInducedTreeSize G : ℝ) * (twoDominationNumber G : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- The 2-domination number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ twoDominationNumber G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture143
