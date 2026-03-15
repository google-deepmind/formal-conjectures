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

This is a variant of the "happy ending problem"
([Problem 107](https://www.erdosproblems.com/107)), which asks the same question without the
empty interior restriction.

[Er78c] Erdős, P. (1978).

[Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_,
Combinatorica 1 (1981), 25–42.

[Er82e] Erdős, P., _Problems and results on finite and infinite graphs_. Recent advances
in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1982).

[Er83c] Erdős, P., _Old and new problems in combinatorial analysis and graph theory_, 1983.

[Er97e] Erdős, P., _Some of my favourite problems which recently have been solved_,
Proc. Int. Conf. on Discrete Math. (1997), 527–533.

[Ha78] Harborth, H., _Konvexe Fünfecke in ebenen Punktmengen_. Elem. Math. 33 (1978), 116-118.

[Ho83] Horton, J. D., _Sets with no empty convex 7-gons_. Canad. Math. Bull. 26 (1983), 482-484.

[Ni07] Nicolás, C. M., _The empty hexagon theorem_. Discrete Comput. Geom. 38 (2007), 389-397.

[Ge08] Gerken, T., _Empty convex hexagons in planar point sets_. Discrete Comput. Geom. 39 (2008),
239-272.

[HeSc24] Heule, M. J. H. and Scheucher, M., _Happy ending: An empty hexagon in every set of 30
points_. J. ACM 71 (2024).

OEIS: [A381776](https://oeis.org/A381776)
-/

open Set EuclideanGeometry

namespace Erdos216

/--
A point set $S$ contains an empty convex $k$-gon if there exists a subset $T \subseteq S$
of exactly $k$ points such that:
1. $T$ is in convex position (the $k$ points form the vertices of a convex polygon), and
2. no other point of $S$ lies in the interior of the convex hull of $T$.
-/
def HasEmptyConvexKGon (S : Finset ℝ²) (k : ℕ) : Prop :=
  ∃ T : Finset ℝ², T ⊆ S ∧ T.card = k ∧
    ConvexIndep (↑T : Set ℝ²) ∧
    ∀ p ∈ S, p ∉ T → p ∉ interior (convexHull ℝ (↑T : Set ℝ²))

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
      ∃ N : ℕ, ∀ (S : Finset ℝ²),
        NonTrilinear (↑S : Set ℝ²) → N ≤ S.card →
        HasEmptyConvexKGon S k := by
  sorry

/--
Horton [Ho83] showed that for $k \geq 7$, there exist arbitrarily large point
sets in general position with no empty convex $k$-gon. Thus $g(k)$ does not
exist for $k \geq 7$.
-/
@[category research solved, AMS 52]
theorem erdos_216_horton : ∀ k : ℕ, 7 ≤ k → ∀ N : ℕ,
    ∃ S : Finset ℝ²,
      NonTrilinear (↑S : Set ℝ²) ∧ N ≤ S.card ∧ ¬HasEmptyConvexKGon S k := by
  sorry

/--
The existence of $g(6)$ was independently proved by Nicolás [Ni07] and
Gerken [Ge08]. The exact value $g(6) = 30$ was determined by
Heule and Scheucher [HeSc24].
-/
@[category research solved, AMS 52]
theorem erdos_216_g6 :
    ∃ N : ℕ, ∀ (S : Finset ℝ²),
      NonTrilinear (↑S : Set ℝ²) → N ≤ S.card →
      HasEmptyConvexKGon S 6 := by
  sorry

end Erdos216
