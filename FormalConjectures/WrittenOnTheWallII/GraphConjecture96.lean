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
# Written on the Wall II - Conjecture 96

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace WrittenOnTheWallII.GraphConjecture96

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- `distEven G v` counts the number of vertices at even distance from `v` in `G`. -/
noncomputable def distEven (G : SimpleGraph α) (v : α) : ℕ :=
  (Finset.univ.filter (fun w => Even (G.dist v w))).card

/--
WOWII [Conjecture 96](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

For a simple connected graph `G`,
`α(G) ≤ 1 + min_v distEven(v) · (max_v l(v) - 1)`
where `α(G) = G.indepNum` is the independence number,
`distEven(v)` is the number of vertices at even distance from `v`, and
`max_v l(v)` is the maximum independence number of a vertex neighbourhood.
-/
@[category research open, AMS 5]
theorem conjecture96 (G : SimpleGraph α) (h : G.Connected) :
    let minDistEven := (Finset.univ.image (distEven G)).min' (by simp)
    let maxL := (Finset.univ.image (fun v => indepNeighborsCard G v)).max' (by simp)
    (G.indepNum : ℝ) ≤ 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1) := by
  sorry

-- Sanity checks

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

/-- The independence number is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.indepNum := Nat.zero_le _

end WrittenOnTheWallII.GraphConjecture96
