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

Erdős–Moser conjecture: if $n$ points in $\mathbb{R}^2$ are in convex position, then the number
of pairs at unit distance is $O(n)$.
-/

namespace Erdos96

/--
A finite set of points in $\mathbb{R}^2$ is in convex position if no point lies in the
convex hull of the remaining points. Equivalently, the points are the vertices
of a convex polygon.
-/
def ConvexPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of ordered pairs of distinct points in $P$ that are at unit distance.
(Using ordered pairs; the number of unordered pairs is exactly half this,
so the $O(n)$ bound is equivalent.)
-/
noncomputable def unitDistancePairCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/--
Erdős Problem 96 (Erdős–Moser conjecture):
If $n$ points in $\mathbb{R}^2$ form a convex polygon (are in convex position), then there
are $O(n)$ many pairs which are distance $1$ apart.

Formally: there exists an absolute constant $C > 0$ such that for every finite
set $P$ of points in $\mathbb{R}^2$ in convex position, the number of (ordered) pairs at
unit distance is at most $C \cdot |P|$.
-/
@[category research open, AMS 52]
theorem erdos_96 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      (unitDistancePairCount P : ℝ) ≤ C * (P.card : ℝ) := by
  sorry

end Erdos96
