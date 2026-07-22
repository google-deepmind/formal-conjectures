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
# Erdős Problem 94

*References:*
- [erdosproblems.com/94](https://www.erdosproblems.com/94)
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*. Eureka
  (1992), 44-48.
- [Er97c] Erdős, Paul, *Some of my favorite problems and results*. The mathematics of Paul Erdős, I
  (1997), 47-67.
- [LeTh95] Lefmann, Hanno and Thiele, Torsten, *Point sets with distinct distances*. Combinatorica
  (1995), 379-408.
-/

open Filter EuclideanGeometry

namespace Erdos94

/-- The set of distances $\{u_1,\ldots,u_t\}$ determined by a finite set of points in
$\mathbb{R}^2$. -/
noncomputable def distanceSet (P : Finset ℝ²) : Finset ℝ :=
  P.offDiag.image fun p => dist p.1 p.2

/-- The number $f(u)$ of unordered pairs of distinct points of $P$ which are at distance $u$
apart. -/
noncomputable def distanceMultiplicity (P : Finset ℝ²) (u : ℝ) : ℕ :=
  (P.offDiag.filter (fun p => dist p.1 p.2 = u)).card / 2

/-- The regular $n$-gon inscribed in the unit circle. -/
noncomputable def regularNGon (n : ℕ) : Finset ℝ² :=
  (Finset.range n).image fun k : ℕ =>
    !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

/--
Suppose $n$ points in $\mathbb{R}^2$ determine a convex polygon and the set of distances between
them is $\{u_1,\ldots,u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs of
points. Then
\[\sum_i f(u_i)^2 \ll n^3.\]

In [Er97c] Erdős claims that Fishburn solved this, but gives no reference.
-/
@[category research solved, AMS 5 52]
theorem erdos_94 : ∃ C > (0 : ℝ), ∀ P : Finset ℝ², ConvexIndep (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/--
Note it is trivial that $\sum f(u_i)=\binom{n}{2}$.
-/
@[category test, AMS 5 52]
theorem erdos_94.variants.sum_multiplicity (P : Finset ℝ²) :
    ∑ u ∈ distanceSet P, distanceMultiplicity P u = P.card.choose 2 := by
  sorry

/--
Lefmann and Theile [LeTh95] prove a stronger version of this question, that
\[\sum_i f(u_i)^2 \ll n^3\]
under the weaker assumption that no three points are on a line.
-/
@[category research solved, AMS 5 52]
theorem erdos_94.variants.no_three_on_a_line : ∃ C > (0 : ℝ), ∀ P : Finset ℝ²,
    NonTrilinear (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/--
Erdős and Fishburn also make the stronger conjecture that $\sum f(u_i)^2$ is maximal for the
regular $n$-gon (for large enough $n$).
-/
@[category research open, AMS 5 52]
theorem erdos_94.variants.regular_ngon : ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℝ²,
    P.card = n → ConvexIndep (P : Set ℝ²) →
    ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  sorry

end Erdos94
