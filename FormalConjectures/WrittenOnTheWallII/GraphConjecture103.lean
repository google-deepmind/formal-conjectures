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
# Written on the Wall II - Conjecture 103

**Verbatim statement (WOWII #103, status O):**
> If G is a simple connected graph, then α(G) ≤ FLOOR[b(G) - LN[average of ecc(v)]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj103


*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture103

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 103](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`α(G) ≤ ⌊b(G) − ln(ecc_avg(G))⌋`
where `α(G) = G.indepNum` is the independence number,
`b(G)` is the largest induced bipartite subgraph size, and
`ecc_avg(G) = G.averageEccentricity` is the average eccentricity of `G`
(from `FormalConjecturesForMathlib`).
Uses `Real.log` (natural logarithm).
-/
@[category research open, AMS 5]
theorem conjecture103 (G : SimpleGraph α) (h : G.Connected) :
    (G.indepNum : ℝ) ≤ ⌊b G - Real.log (averageEccentricity G)⌋ := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- `Real.log` of a positive real is well-defined. -/
@[category test, AMS 5]
example : Real.log 1 = 0 := Real.log_one

end WrittenOnTheWallII.GraphConjecture103
