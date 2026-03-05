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
# Erdős Problem 94

*Reference:* [erdosproblems.com/94](https://www.erdosproblems.com/94)

For $n$ points in convex position with distance multiplicities $f(u_i)$, the sum
$\sum_i f(u_i)^2$ is $O(n^3)$. Proved by Lefmann and Thiele.

[LeTh95] Lefmann, H. and Thiele, T., _Point sets with distinct distances_.
Combinatorica 15 (1995), 379–408.
-/

namespace Erdos94

/--
A finite set of points in $\mathbb{R}^2$ is in convex position if no point lies in
the convex hull of the remaining points. Equivalently, all points are
vertices of their convex hull (they form a convex polygon).
-/
def ConvexPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A : Set (EuclideanSpace ℝ (Fin 2))) \ {p})

/--
The count of ordered quadruples $(a, b, c, d)$ from $A$ with $a \neq b$, $c \neq d$,
and $\operatorname{dist}(a, b) = \operatorname{dist}(c, d)$. This equals
$4 \cdot \sum_i f(u_i)^2$ where $f(u_i)$ counts unordered pairs at distance $u_i$.
-/
noncomputable def distSqSum (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  let E := EuclideanSpace ℝ (Fin 2)
  Set.ncard {x : E × E × E × E |
    x.1 ∈ (A : Set E) ∧ x.2.1 ∈ (A : Set E) ∧
    x.2.2.1 ∈ (A : Set E) ∧ x.2.2.2 ∈ (A : Set E) ∧
    x.1 ≠ x.2.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
    dist x.1 x.2.1 = dist x.2.2.1 x.2.2.2}

/--
Suppose $n$ points in $\mathbb{R}^2$ are in convex position (they form the vertices of
a convex polygon). Let $\{u_1, \ldots, u_t\}$ be the set of distinct pairwise
distances, and let $f(u_i)$ denote the number of pairs at distance $u_i$. Then
$$\sum_i f(u_i)^2 \ll n^3.$$

This was proved by Lefmann and Thiele [LeTh95] under the weaker
assumption that no three points are collinear.
-/
@[category research solved, AMS 5 52]
theorem erdos_94 :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      ConvexPosition A →
      (distSqSum A : ℝ) ≤ C * (A.card : ℝ) ^ 3 := by
  sorry

end Erdos94
