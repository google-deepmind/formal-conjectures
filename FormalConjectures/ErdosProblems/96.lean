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

Erdős and Fishburn conjectured the stronger bound of $2n$.

## Known bounds

- The best known upper bound is $n \log_2 n + 4n$ [Ag15].
- The $O(n \log n)$ bound was first proved by Füredi [Fu90], with a simplified proof
  by Brass and Pach [BrPa01].
- Edelsbrunner and Hajnal [EdHa91] constructed $n$ points in convex position with
  $2n - 7$ unit-distance pairs, giving the best known lower bound.

## Related problems

Problem 97 would imply a positive answer; see also Problem 90.

## References

- [Ag15] Aggarwal, A., _On unit distances in a convex polygon_. Discrete Math. (2015), 88-92.
- [BrPa01] Brass, P., Pach, J., _The maximum number of times the same distance can occur among
  the vertices of a convex n-gon is O(n log n)_. J. Combin. Theory Ser. A (2001), 178-179.
- [EdHa91] Edelsbrunner, H., Hajnal, P., _A lower bound on the number of unit distances between
  the vertices of a convex polygon_. J. Combin. Theory Ser. A (1991), 312-316.
- [Fu90] Füredi, Z., _The maximum number of unit distances in a convex n-gon_.
  J. Combin. Theory Ser. A (1990), 316-320.
-/

open EuclideanGeometry

namespace Erdos96

/--
The number of ordered pairs of distinct points in $P$ that are at unit distance.
(Using ordered pairs; the number of unordered pairs is exactly half this,
so the $O(n)$ bound is equivalent.)
-/
noncomputable def unitDistancePairCount (P : Finset ℝ²) : ℕ :=
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
    ∀ (P : Finset ℝ²),
      ConvexIndep (↑P : Set ℝ²) →
      (unitDistancePairCount P : ℝ) ≤ C * (P.card : ℝ) := by
  sorry

/--
Erdős–Fishburn conjecture (stronger variant of Problem 96):
The exact upper bound on the number of unit-distance pairs among $n$ points in convex
position is $2n$ (for sufficiently large $n$). Edelsbrunner and Hajnal [EdHa91] showed
that $2n - 7$ is achievable, so the conjectured bound would be tight up to a constant.

Here we state: for all sufficiently large convex-position point sets, the number of
unordered unit-distance pairs is at most $2n$.
-/
@[category research open, AMS 52]
theorem erdos_96_fishburn :
    ∃ N : ℕ, ∀ (P : Finset ℝ²),
      ConvexIndep (↑P : Set ℝ²) →
      N ≤ P.card →
      unitDistancePairCount P ≤ 2 * P.card := by
  sorry

end Erdos96
