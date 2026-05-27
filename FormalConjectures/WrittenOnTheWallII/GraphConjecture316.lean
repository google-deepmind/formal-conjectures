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
# Written on the Wall II - Conjecture 316

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture316

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/--
WOWII [Conjecture 316](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

Let `G` be a simple connected graph and let `P` denote the set of pendant vertices
(vertices of degree 1). If `|P| ≥ deg_avg(G)`, then `G` is well totally dominated,
where `deg_avg(G)` is the average degree of `G`.
-/
@[category research open, AMS 5]
theorem conjecture316 (G : SimpleGraph α) [DecidableRel G.Adj] (hG : G.Connected)
    (h : (averageDegree G : ℚ) ≤ (pendantVertices G).card) :
    IsWellTotallyDominated G := by
  sorry

-- Sanity checks

/-- The average degree of the edgeless graph on 3 vertices is 0. -/
@[category test, AMS 5]
example : averageDegree (⊥ : SimpleGraph (Fin 3)) = 0 := by
  unfold averageDegree; simp [Fintype.card_fin]

/-- In `P₃` (path 0-1-2), the average degree is 4/3 and there are 2 pendant vertices. -/
@[category test, AMS 5]
example : averageDegree (SimpleGraph.fromEdgeSet {s(0,1), s(1,2)} : SimpleGraph (Fin 3)) = 4/3 := by
  unfold averageDegree; decide +native

end WrittenOnTheWallII.GraphConjecture316
