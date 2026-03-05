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
# Erdős Problem 216

*Reference:* [erdosproblems.com/216](https://www.erdosproblems.com/216)

Does $g(k)$ exist for all $k \geq 3$, where $g(k)$ is the smallest $N$ such that any set of $N$
points in general position in $\mathbb{R}^2$ contains an empty convex $k$-gon?

[Ha78] Harborth, H., _Konvexe Fünfecke in ebenen Punktmengen_. Elem. Math. 33 (1978), 116-118.

[Ho83] Horton, J. D., _Sets with no empty convex 7-gons_. Canad. Math. Bull. 26 (1983), 482-484.

[Ni07] Nicolás, C. M., _The empty hexagon theorem_. Discrete Comput. Geom. 38 (2007), 389-397.

[Ge08] Gerken, T., _Empty convex hexagons in planar point sets_. Discrete Comput. Geom. 39 (2008),
239-272.

[HeSc24] Heule, M. J. H. and Scheucher, M., _Happy ending: An empty hexagon in every set of 30
points_. J. ACM 71 (2024).
-/

open Set

namespace Erdos216

/-- A point in the Euclidean plane $\mathbb{R}^2$. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
A finite set of points in $\mathbb{R}^2$ is in general position if no three distinct
points are collinear (i.e., for any three distinct points, the third does
not lie on the affine line through the other two).
-/
def InGeneralPosition (S : Finset Point) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
    p₃ ∉ (affineSpan ℝ ({p₁, p₂} : Set Point) : Set Point)

/--
A finite set of points is in convex position if no point lies in the
convex hull of the remaining points.
-/
def InConvexPosition (S : Finset Point) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set Point)

/--
A point set $S$ contains an empty convex $k$-gon if there exists a subset $T \subseteq S$
of exactly $k$ points such that:
1. $T$ is in convex position (the $k$ points form the vertices of a convex polygon), and
2. no other point of $S$ lies in the interior of the convex hull of $T$.
-/
def HasEmptyConvexKGon (S : Finset Point) (k : ℕ) : Prop :=
  ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧
    InConvexPosition T ∧
    ∀ p ∈ S, p ∉ T → p ∉ interior (convexHull ℝ (↑T : Set Point))

/--
Let $g(k)$ be the smallest integer $N$ (if it exists) such that any set of $N$
points in general position in $\mathbb{R}^2$ contains an empty convex $k$-gon (a convex
$k$-gon with no point of the set in its interior). Does $g(k)$ exist for
all $k \geq 3$?

Known results:
- $g(3) = 3$ (trivial) and $g(4) = 5$ (Erdős).
- $g(5) = 10$ (Harborth [Ha78]).
- $g(6)$ exists (Nicolás [Ni07], Gerken [Ge08]), and $g(6) = 30$
  (Heule–Scheucher [HeSc24]).
- DISPROVED for $k \geq 7$: Horton [Ho83] constructed arbitrarily large point
  sets in general position with no empty convex $7$-gon, so $g(k)$ does not
  exist for $k \geq 7$.
-/
@[category research solved, AMS 52]
theorem erdos_216 : answer(False) ↔
    ∀ k : ℕ, 3 ≤ k →
      ∃ N : ℕ, ∀ (S : Finset Point),
        InGeneralPosition S → N ≤ S.card →
        HasEmptyConvexKGon S k := by
  sorry

end Erdos216
