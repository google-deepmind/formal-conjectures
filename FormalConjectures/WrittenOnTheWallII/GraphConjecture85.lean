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

import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 85

**Verbatim statement (WOWII #85, status O):**
> If G is a simple connected graph, then tree(G) ≥ CEIL[sqrt(1 + 2*minimum of dist_even(v))]

**Source:** http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj85

This conjecture is **false**: Kuber Mehta found the counterexample `G = C₅[K₄]`
(the 5-cycle with each vertex replaced by a `K₄`, consecutive cliques completely
joined), for which `tree(G) = 4` while the conjectured lower bound is
`⌈√(1 + 2·9)⌉ = 5`. The same graph also refutes WOWII Conjecture 63. We
therefore record the statement as disproved, using the `answer(False) ↔ ...`
pattern of Conjectures 23/24/25.

*References:*
- [E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
- [Counterexample certificates for WOWII 63 and 85 (Kuber Mehta)](https://github.com/Kuberwastaken/wowii-63-85-counterexample)
-/

namespace WrittenOnTheWallII.GraphConjecture85

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/--
WOWII [Conjecture 85](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
(disproved, 2026):

For a simple connected graph `G`,
`tree(G) ≥ ⌈√(1 + 2 · min_v distEven(v))⌉`
where `tree(G)` is the number of vertices in a largest induced tree and
`distEven(v)` is the number of vertices at even distance from `v`.

Disproved by the counterexample `C₅[K₄]` (Kuber Mehta, 2026): there
`tree(G) = 4 < 5 = ⌈√19⌉`. More generally, in `C₅[K_m]` every induced tree has
at most 4 vertices while the right-hand side grows like `2√m`.
-/
@[category research solved, AMS 5]
theorem conjecture85 : answer(False) ↔
    ∀ {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α],
      ∀ (G : SimpleGraph α) (_ : G.Connected),
        let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
        ⌈Real.sqrt (1 + 2 * (minDistEven : ℝ))⌉ ≤ (G.largestInducedTreeSize : ℝ) := by
  sorry

-- Sanity checks

/-- The `largestInducedTreeSize` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ largestInducedTreeSize G := Nat.zero_le _

/-- `Real.sqrt` is nonneg. -/
@[category test, AMS 5]
example (x : ℝ) : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x

end WrittenOnTheWallII.GraphConjecture85
