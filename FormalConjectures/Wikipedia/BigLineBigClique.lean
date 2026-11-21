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
# The big-line-big-clique conjecture

A "big line" in a finite planar point set is a set of `ℓ` collinear points. A
"big clique" is a set of `k` points that are pairwise *visible*: two points are
visible if the open segment between them contains no other point of the set,
i.e. they form a clique in the *visibility graph*.

Kára, Pór, and Wood (2005) conjectured that these are the only two obstructions
to unbounded structure: for all `k` and `ℓ` there is an `n` such that every
`n`-point set contains `ℓ` collinear points or `k` pairwise-visible points (or
both). This is a Ramsey-type statement in the Erdős–Szekeres family.

The conjecture is open in general. It is known for `ℓ ≤ 3`: point sets with no
three collinear (general position) always contain a big clique, by the
Erdős–Szekeres / happy-ending theorem (`FormalConjectures.Wikipedia.HappyEndingProblem`,
`FormalConjectures.ErdosProblems.«107»`) together with the fact that in convex
position all points are mutually visible.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Big-line-big-clique_conjecture)
- [KPW05] J. Kára, A. Pór, and D. R. Wood, *On the chromatic number of the
  visibility graph of a set of points in the plane*, Discrete & Computational
  Geometry 34 (2005), 497–506.
  [doi:10.1007/s00454-005-1177-z](https://doi.org/10.1007/s00454-005-1177-z).
-/

open EuclideanGeometry

namespace BigLineBigClique

/-- `S` contains a *big clique* of size `k`: a `k`-element subset whose points
are pairwise visible in `S` (a clique of size `k` in the visibility graph). The
visibility relation `EuclideanGeometry.Visible` lives in `Geometry.2d`. -/
def HasBigClique (k : ℕ) (S : Set ℝ²) : Prop :=
  ∃ C : Finset ℝ², C.card = k ∧ ↑C ⊆ S ∧
    (C : Set ℝ²).Pairwise (Visible S)

/-- `S` contains a *big line* of size `ℓ`: `ℓ` collinear points of `S`. This is the
negation of `EuclideanGeometry.NonCollinearFor ℓ` (which says no `ℓ` points of `S`
are collinear); we keep the positive "big line" phrasing here for readability. -/
def HasBigLine (ℓ : ℕ) (S : Set ℝ²) : Prop :=
  ∃ L : Finset ℝ², L.card = ℓ ∧ ↑L ⊆ S ∧ Collinear ℝ (L : Set ℝ²)

/--
**The big-line-big-clique conjecture (Kára–Pór–Wood).**
For all `k` and `ℓ` there is an `n` such that every planar point set with at
least `n` points contains `ℓ` collinear points or `k` pairwise-visible points.
-/
@[category research open, AMS 52]
theorem big_line_big_clique :
    ∀ k ℓ : ℕ, ∃ n : ℕ, ∀ S : Finset ℝ², n ≤ S.card →
      HasBigLine ℓ (↑S) ∨ HasBigClique k (↑S) := by
  sorry

namespace variants

/--
The conjecture holds for `ℓ ≤ 3`: if a point set has no three collinear points
(general position), it contains an arbitrarily large clique in the visibility
graph. Equivalently, for every `k` there is an `n` such that every set of `n`
points contains `3` collinear points or a big clique of size `k`.
-/
@[category research solved, AMS 52]
theorem big_line_big_clique_line_three (k : ℕ) :
    ∃ n : ℕ, ∀ S : Finset ℝ², n ≤ S.card →
      HasBigLine 3 (↑S) ∨ HasBigClique k (↑S) := by
  sorry

end variants

end BigLineBigClique
