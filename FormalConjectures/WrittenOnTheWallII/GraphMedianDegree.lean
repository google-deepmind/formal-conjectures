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
# Graph Median Degree Invariant

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

## Definition

The **median degree** of a graph `G` on `n` vertices is the middle value of the
sorted degree sequence.  Concretely, we sort the list of degrees of all vertices
in non-decreasing order and return the element at index `n / 2` (integer
division), which is the lower median when `n` is even.

For the empty graph (`n = 0`) the median degree is defined to be 0.

## Conjecture

For any simple connected graph `G` with at least 2 vertices,
`1 ≤ medianDegree G`.

In a connected graph every vertex has degree at least 1, so every entry of the
sorted degree sequence is at least 1; in particular the middle entry is ≥ 1.
-/

namespace WrittenOnTheWallII.GraphMedianDegree

open Classical SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **median degree** of `G`.

We form the list of degrees of all vertices, sort it in non-decreasing order, and
return the element at position `Fintype.card α / 2`.  When the graph has no
vertices the degree list is empty; we return 0 in that case. -/
noncomputable def medianDegree (G : SimpleGraph α) : ℕ :=
  if Fintype.card α = 0 then 0
  else
    let degList : List ℕ := Finset.univ.toList.map (fun v => G.degree v)
    let sorted : List ℕ := degList.mergeSort (· ≤ ·)
    sorted.getD (Fintype.card α / 2) 0

/--
**WOWII-style conjecture**: For a simple connected graph `G` with at least
2 vertices, `1 ≤ medianDegree G`.

In a connected graph, every vertex has degree at least 1.  Hence the sorted degree
sequence consists entirely of values ≥ 1, and in particular the element at the
median position is ≥ 1.
-/
@[category research open, AMS 5]
theorem medianDegree_pos (G : SimpleGraph α) [DecidableRel G.Adj]
    (hconn : G.Connected) :
    1 ≤ medianDegree G := by
  sorry

-- Sanity checks

/-- In `K₃`, all degrees are 2, so the sorted sequence is `[2, 2, 2]` and the
median (at index 1) is 2. -/
@[category test, AMS 5]
example : medianDegree (⊤ : SimpleGraph (Fin 3)) = 2 := by
  unfold medianDegree
  sorry

/-- In the path `P₄` (0–1–2–3), degrees are `[1, 2, 2, 1]`.  Sorted: `[1, 1, 2, 2]`.
The median at index `4 / 2 = 2` is 2. -/
@[category test, AMS 5]
example : medianDegree
    (SimpleGraph.fromEdgeSet {s(0,1), s(1,2), s(2,3)} : SimpleGraph (Fin 4)) = 2 := by
  unfold medianDegree
  sorry

/-- `medianDegree` is nonneg. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 5)) : 0 ≤ medianDegree G :=
  Nat.zero_le _

end WrittenOnTheWallII.GraphMedianDegree
