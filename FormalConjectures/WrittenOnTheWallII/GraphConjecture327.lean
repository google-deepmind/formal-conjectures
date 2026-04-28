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
# Written on the Wall II - Conjecture 327

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture327

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 327](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph. If `3 · γ(G) = γ_i(G)`, then `G` is well
totally dominated, where `γ(G)` is the domination number of `G` and `γ_i(G)` is
the independent domination number of `G`.
-/
@[category research open, AMS 5]
theorem conjecture327 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : 3 * G.dominationNumber = G.indepDominationNumber) :
    IsWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- In `K₂`, the max degree is 1 (each vertex has exactly one neighbor). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 2)).maxDegree = 1 := by decide +native

/-- In the path graph `P₃`, vertex 1 has degree 2. -/
@[category test, AMS 5]
example : (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)).degree 1 = 2 := by
  decide +native

end WrittenOnTheWallII.GraphConjecture327
