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
# Erdős Problem 92

*Reference:* [erdosproblems.com/92](https://www.erdosproblems.com/92)
-/

open Filter
open scoped EuclideanGeometry

namespace Erdos92

/--
For a given point `x` and a set of other points, this function finds the maximum number of points
that lie on a single circle centered at `x`. It does this by grouping the other points by their
distance to `x` and finding the size of the largest group.
-/
noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  let otherPoints := points.erase x
  let distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

/--
This property holds for a set of points `A` if every point `x` in `A` has at least `k` other
points from `A` that are equidistant from `x`.
-/
def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A


/--
The set of all possible values `k` for which there exists a set of `n` points
satisfying the `hasMinEquidistantProperty k`. The function `f(n)` will be the supremum of this set.
-/
noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

/--
A sanity check to ensure the set of possible `f(n)` values is bounded above. A trivial bound is
`n-1`, since any point can have at most `n-1` other points equidistant from it.
This ensures `sSup` is well-defined.
-/
@[category test, AMS 52]
theorem possible_f_values_BddAbove (n : ℕ) : BddAbove (possible_f_values n) := by
  use n - 1
  rintro k ⟨points, h_card, h_prop⟩
  unfold Erdos92.hasMinEquidistantProperty at *
  unfold Erdos92.maxEquidistantPointsAt at *
  sorry


/--
Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb^2$
in which every $x \in A$ has at least $f(n)$ points in $A$ equidistant from $x$.
-/
noncomputable def f (n : ℕ) : ℕ := sSup <| possible_f_values n


/--
Is it true that $f(n)\leq n^{o(1)}$?
-/
@[category research open, AMS 52]
theorem erdos_92.variants.weak : (∃ o : ℕ → ℝ,
  o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ n, (f n : ℝ) ≤ n^(o n)) ↔ answer(sorry) := by
sorry

/--
Or even $f(n) < n^{c/\log\log n}$ for some constant $c > 0$?
-/
@[category research open, AMS 52]
theorem erdos_92.variants.strong :
  (∃ c > 0, ∀ n, (f n : ℝ) ≤ n^(c / (n : ℝ).log.log)) ↔ answer(sorry) := by
sorry

-- TODO(firsching): formalize the rest of the remarks

end Erdos92
