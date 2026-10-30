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
module

public import FormalConjecturesUtil
/-!
# Graph Degree Mode Maximum Invariant

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphModeMax

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

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
For any simple graph `G` on `n ≥ 2` vertices,
`modeDegreeMin G + modeDegreeMax Gᶜ ≥ Fintype.card α - 1`.

Complementation sends degree `d` to `n - 1 - d` and preserves its frequency.
Thus the smallest modal degree of `G` and the largest modal degree of `Gᶜ`
sum to `n - 1`, which gives the stated bound.
-/
@[category textbook, AMS 5]
theorem modeDegreeMin_add_modeDegreeMax_compl (G : SimpleGraph α) [DecidableRel G.Adj] :
    Fintype.card α - 1 ≤ modeDegreeMin G + modeDegreeMax Gᶜ := by
  sorry

-- Sanity checks

/-- In `K₃`, every vertex has degree 2.  So `modeDegreeMax K₃ = 2`. -/
@[category test, AMS 5]
example : modeDegreeMax (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold modeDegreeMax maxDegreeCount countDegreeK
  sorry

/-- `modeDegreeMin ≤ modeDegreeMax` holds trivially for any graph. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] : modeDegreeMin G ≤ modeDegreeMax G := by
  sorry

/-- `modeDegreeMax` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] : 0 ≤ modeDegreeMax G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphModeMax
