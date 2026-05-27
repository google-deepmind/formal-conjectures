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
# Written on the Wall II - Conjecture 133

**Verbatim statement (WOWII #133, status O):**
> If G is a simple connected graph, then path(G) ≥ rad(G)+ [average of λ(v)]^^χC4

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj133


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

`cC4 G` counts the number of **induced** 4-cycles in `G`.  We use the
upstream `SimpleGraph.countInducedC4` (and the auxiliary `isInducedC4`)
from `FormalConjecturesForMathlib/.../Invariants.lean`, which counts ordered
4-tuples of distinct vertices forming an induced 4-cycle and divides by `4!`.
-/

namespace WrittenOnTheWallII.GraphConjecture133

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 133](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`path(G) ≥ rad(G) + ⌊avg_v l(v)⌋ ^ cC4(G)`
where `path(G)` is the floor of the average distance, `rad(G)` is the radius
(minimum eccentricity, as a natural number), `avg_v l(v) = l G` is the average
independence number of vertex neighbourhoods, and `cC4(G)` is the number of
induced C₄ subgraphs.
-/
@[category research open, AMS 5]
theorem conjecture133 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let rad := (minEccentricity G).toNat
    let cC4 := countInducedC4 G
    (rad : ℝ) + (⌊l G⌋ : ℝ) ^ cC4 ≤ (path G : ℝ) := by
  sorry

-- Sanity checks

/-- The `path G` invariant is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (path G : ℝ) := Nat.cast_nonneg _

/-- `minEccentricity` toNat is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ (minEccentricity G).toNat := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture133
