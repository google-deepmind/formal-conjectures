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
# Written on the Wall II - Conjecture 61

**Verbatim statement (WOWII #61, status O):**
> If G is a simple connected graph, then f(G) ≥ res(G)+ CEIL[diam(G)/3]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj61


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture61

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 61](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`, the size `f(G)` of a largest induced forest satisfies
`f(G) ≥ residue(G) + ⌈diam(G) / 3⌉`, where `residue(G)` is the Havel-Hakimi residue
and `diam(G)` is the diameter of `G`.

See: Favaron, Mahéo, Saclé (1991) for the residue; DeLaVina's Graffiti.pc for the conjecture.
-/
@[category research open, AMS 5]
theorem conjecture61 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (residue G : ℝ) + ⌈(G.diam : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- The residue of `K₂` equals 0. -/
@[category test, AMS 5]
example : residue (⊤ : SimpleGraph (Fin 2)) = 0 := by
  unfold residue; decide +native

end WrittenOnTheWallII.GraphConjecture61
