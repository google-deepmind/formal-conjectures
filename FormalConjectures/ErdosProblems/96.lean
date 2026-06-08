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
# Erdős Problem 96

*Reference:* [erdosproblems.com/96](https://www.erdosproblems.com/96)
-/

open Filter
open EuclideanGeometry
open scoped EuclideanGeometry

namespace Erdos96
open Finset

/--
The set of all possible numbers of unit distances determined by the vertices of a convex
$n$-gon.
-/
noncomputable def convexUnitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistancePairsCount points | (points : Finset ℝ²) (_ : points.card = n) (_ : ConvexIndep points)}

/--
This lemma confirms that the set of possible unit-distance counts is bounded above, which
ensures that taking the supremum (`sSup`) is a well-defined operation. The trivial upper bound is
the total number of pairs of points, $\binom{n}{2}$.
-/
@[category test, AMS 52]
theorem convexUnitDistanceCounts_bddAbove (n : ℕ) : BddAbove <| convexUnitDistanceCounts n := by
  unfold convexUnitDistanceCounts
  unfold unitDistancePairsCount
  use n.choose 2
  rintro _ ⟨points, rfl, _, rfl⟩
  rw [points.card.choose_two_right]
  have hle : (points.offDiag.filter fun p : ℝ² × ℝ² => dist p.1 p.2 = 1).card ≤
      points.offDiag.card := by
    exact card_filter_le _ _
  have hdiv := Nat.div_le_div_right (c := 2) hle
  simpa [offDiag_card, Nat.mul_sub_left_distrib, mul_one] using hdiv

/--
The **maximum number of unit distances** determined by the vertices of a convex $n$-gon.
This function is often denoted as $U_c(n)$ in combinatorics.
-/
noncomputable def maxConvexUnitDistances (n : ℕ) : ℕ :=
  sSup (convexUnitDistanceCounts n)

/--
If $n$ points in $\mathbb{R}^2$ form a convex polygon then there are $O(n)$ many pairs which are
distance $1$ apart.
-/
@[category research open, AMS 52]
theorem erdos_96 :
    answer(sorry) ↔ (fun n => (maxConvexUnitDistances n : ℝ)) =O[atTop] fun n => (n : ℝ) := by
  sorry

end Erdos96
