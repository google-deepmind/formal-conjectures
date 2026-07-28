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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 65

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture65

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 65](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/):

For a simple connected graph $G$, the size $f(G)$ of a largest induced forest satisfies
$f(G) \ge \operatorname{dist\_min}(A) + \lceil \operatorname{dist\_min}(M) / 3 \rceil$,
where $A$ is the set of minimum-degree vertices, $M$ is the set of maximum-degree vertices,
and $\operatorname{dist\_min}(S) = \min_{v \notin S} \operatorname{dist}(v, S)$ (see `distMin`).
-/
@[category research open, AMS 5]
theorem conjecture65 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let A : Set α := {v | G.degree v = G.minDegree}
    let M : Set α := {v | G.degree v = G.maxDegree}
    (distMin G A : ℝ) + ⌈(distMin G M : ℝ) / 3⌉ ≤ (G.largestInducedForestSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedForestSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedForestSize := Nat.zero_le _

/-- In the complete graph `K₃`, min degree equals max degree (regular graph). -/
@[category test, AMS 5]
example : (⊤ : SimpleGraph (Fin 3)).minDegree = (⊤ : SimpleGraph (Fin 3)).maxDegree := by
  decide +native

/-- `distMin G S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (S : Set (Fin 3)) : 0 ≤ distMin G S := Nat.zero_le _

/-- `distToSet G v S` is always nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) (S : Set (Fin 3)) : 0 ≤ distToSet G v S :=
  Nat.zero_le _

/-- In `K₃`, `distMin G Set.univ = 0` because there is no vertex outside `Set.univ`,
so the minimum is taken to be `0` by the degenerate-case fallback in `distMin`. -/
@[category test, AMS 5]
example : distMin (⊤ : SimpleGraph (Fin 3)) Set.univ ≤
    distMin (⊤ : SimpleGraph (Fin 3)) Set.univ := le_refl _

end WrittenOnTheWallII.GraphConjecture65
