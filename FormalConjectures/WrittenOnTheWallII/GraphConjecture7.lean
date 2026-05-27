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
# Written on the Wall II - Conjecture 7

**Verbatim statement (WOWII #7, status T):**
> If G is a simple connected graph, then L_s(G) ≥ maximum of λ(v) -1 + n - 2α(G)

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj7


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

**Conjecture 7:** For a connected graph `G`,
`Ls(G) ≥ max_v λ(v) - 1 + n - 2 α(G)`,
where `Ls(G)` is the maximum number of leaves over all spanning trees,
`n = |V(G)|`, `α(G) = G.indepNum`, and `λ(v) = indepNeighborsCard G v` is the
independence number of the neighbourhood of `v`.
-/

namespace WrittenOnTheWallII.GraphConjecture7

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 7](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`L_s(G) ≥ max_v λ(v) - 1 + n - 2 α(G)`,
where `L_s(G)` is the maximum number of leaves over all spanning trees of `G`,
`n = |V(G)|`, `α(G) = G.indepNum` is the independence number, and
`λ(v) = indepNeighborsCard G v` is the independence number of the neighbourhood
of `v`.

WOWII status: proved (DeLaVina, Fajtlowicz, Waller (2002)).
-/
@[category research solved, AMS 5]
theorem conjecture7 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    ((maxL : ℤ) - 1 + (Fintype.card α : ℤ) - 2 * (G.indepNum : ℤ) : ℝ) ≤ Ls G := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture7
