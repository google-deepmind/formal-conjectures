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
# Graph Odd Girth Conjecture

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

The **odd girth** of a graph `G` is the length of a shortest odd cycle.
If `G` is bipartite (has no odd cycles), the odd girth is defined to be 0.

## Conjecture

A well-known result in chromatic graph theory states that for any non-bipartite
graph `G`, its chromatic number satisfies `χ(G) ≥ 3`.  A natural Graffiti.pc–style
strengthening is:

For any non-bipartite connected graph `G`,
`G.chromaticNumber ≥ (oddGirth G + 1) / 2`.
This holds because odd-cycle-containing graphs have chromatic number at least
roughly `oddGirth / (oddGirth − 1) + 1`.  In particular, for `oddGirth = 3`
(triangles present) we get `χ ≥ 2`, and for `oddGirth = 5` we get `χ ≥ 3`.
-/

namespace WrittenOnTheWallII.GraphOddGirth

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **odd girth** of `G` is the length of a shortest odd-length cycle.
Returns 0 if `G` has no odd cycle (i.e., `G` is bipartite or acyclic). -/
noncomputable def oddGirth (G : SimpleGraph α) : ℕ :=
  let oddCycleLengths := {k | Odd k ∧ ∃ v : α, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = k}
  if oddCycleLengths.Nonempty then sInf oddCycleLengths else 0

/-- For a non-bipartite connected graph `G`, the chromatic number satisfies
`χ(G) ≥ (oddGirth(G) + 1) / 2`.

The chromatic number `G.chromaticNumber` is in `ℕ∞`; we compare its natural-number
truncation to ensure well-typed statements. -/
@[category research open, AMS 5]
theorem oddGirth_chromatic_lower_bound (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) (hbip : ¬G.IsBipartite) :
    (oddGirth G + 1) / 2 ≤ G.chromaticNumber.toNat := by
  sorry

-- Sanity checks

/-- The triangle `K₃` has an odd cycle of length 3, so its odd girth is 3. -/
@[category test, AMS 5]
example : oddGirth (⊤ : SimpleGraph (Fin 3)) = 3 := by
  unfold oddGirth
  sorry

/-- The 6-cycle `C₆` is bipartite, so it has no odd cycle; its odd girth is 0. -/
@[category test, AMS 5]
example : oddGirth (cycleGraph 6) = 0 := by
  unfold oddGirth
  sorry

/-- The odd girth of `K₅` is 3 (the shortest cycle is a triangle). -/
@[category test, AMS 5]
example : oddGirth (⊤ : SimpleGraph (Fin 5)) = 3 := by
  unfold oddGirth
  sorry

end WrittenOnTheWallII.GraphOddGirth
