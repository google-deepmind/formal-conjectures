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
import FormalConjectures.WrittenOnTheWallII.GraphMode

/-!
# Graph Degree Mode Maximum Invariant

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definitions

For a graph `G`, recall that `degreeCount G d` is the number of vertices having
degree exactly `d`, and `maxDegreeCount G` is the mode frequency (the highest
frequency among all degree values).

The **mode-max degree** `modeDegreeMax G` is the *largest* degree value that
attains the mode frequency; it is the supremum of the set of modal degree values.
This is the complement of `modeDegreeMin G` (from `GraphMode.lean`), which
picks the *smallest* such degree.

## Conjectures

1. (Trivially TRUE) `modeDegreeMin G ≤ modeDegreeMax G` — the smallest modal
   degree cannot exceed the largest modal degree.

2. (Open) For a graph `G` with complement `Gᶜ`, the sum
   `modeDegreeMin G + modeDegreeMax Gᶜ ≥ Fintype.card α - 1`
   is a WOWII-style conjecture relating modal degrees across complementary graphs.
-/

namespace WrittenOnTheWallII.GraphModeMax

open Classical SimpleGraph WrittenOnTheWallII.GraphMode

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The largest degree value achieving the mode frequency.
Defined as the supremum of the set of modal degree values (those `d` for which
`degreeCount G d = maxDegreeCount G`).  When the graph has no vertices the set
may be empty; by convention `sSup ℕ ∅ = 0`. -/
noncomputable def modeDegreeMax (G : SimpleGraph α) : ℕ :=
  sSup {d | degreeCount G d = maxDegreeCount G}

/--
**modeDegreeMin ≤ modeDegreeMax** (trivially true).

The smallest element of a set of natural numbers cannot exceed the largest element
of the same set.  In particular, for the set of modal degree values,
`modeDegreeMin G ≤ modeDegreeMax G`.
-/
@[category research solved, AMS 5]
theorem modeDegreeMin_le_modeDegreeMax (G : SimpleGraph α) [DecidableRel G.Adj] :
    modeDegreeMin G ≤ modeDegreeMax G := by
  sorry

/--
**WOWII-style open conjecture**: For any simple graph `G` on `n ≥ 2` vertices,
`modeDegreeMin G + modeDegreeMax Gᶜ ≥ Fintype.card α - 1`.

Informally: the smallest modal degree of `G` and the largest modal degree of its
complement `Gᶜ` together "cover" at least `n - 1`.  This is plausible because
complementation exchanges high-degree and low-degree vertices: if many vertices
have a small degree in `G` then many vertices have a large degree in `Gᶜ`.
-/
@[category research open, AMS 5]
theorem modeDegreeMin_add_modeDegreeMax_compl (G : SimpleGraph α) [DecidableRel G.Adj] :
    Fintype.card α - 1 ≤ modeDegreeMin G + modeDegreeMax Gᶜ := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex has degree 2.  So `modeDegreeMax K₃ = 2`. -/
@[category test, AMS 5]
example : modeDegreeMax (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold modeDegreeMax maxDegreeCount degreeCount
  sorry

/-- `modeDegreeMin ≤ modeDegreeMax` holds trivially for any graph. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) : modeDegreeMin G ≤ modeDegreeMax G := by
  sorry

/-- `modeDegreeMax` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ modeDegreeMax G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphModeMax
