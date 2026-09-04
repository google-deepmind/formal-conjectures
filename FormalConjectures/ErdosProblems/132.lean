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
# Erdős Problem 132

*References:*
- [erdosproblems.com/132](https://www.erdosproblems.com/132)
- [CDL25] F. Clemen, A. Dumitrescu, and D. Liu, On multiplicities of interpoint distances. arXiv:2505.04283 (2025).
- [Er84c] Erdős, Paul, Some old and new problems in combinatorial geometry. Convexity and graph theory (Jerusalem, 1981) (1984), 129-136.
- [Er97e] Erdős, Paul, Some of my favourite unsolved problems. Math. Japon. (1997), 527-537.
- [ErFi95] Erdős, Paul and Fishburn, Peter C., Multiplicities of interpoint distances in finite planar sets. Discrete Appl. Math. (1995), 141--147.
- [HoPa34] Hopf, H. and Pannwitz, E., Aufgabe 167. Jber. Deutsch. Math. Verein. (1934), 114.
-/

open Filter EuclideanGeometry
open scoped EuclideanGeometry

namespace Erdos132

/--
The number of **unordered pairs** of distinct points of `P` at distance exactly $d$.
-/
noncomputable def distanceMultiplicity (P : Finset ℝ²) (d : ℝ) : ℕ :=
  (P.offDiag.filter fun p => dist p.1 p.2 = d).card / 2

/--
The set of distances that occur in `P` at least once but between at most $|P|$ pairs of points.
-/
noncomputable def lowMultiplicityDistances (P : Finset ℝ²) : Set ℝ :=
  {d | 0 < distanceMultiplicity P d ∧ distanceMultiplicity P d ≤ P.card}

/--
The minimum, over all configurations of $n$ points in the plane, of the number of distances that
occur at least once but between at most $n$ pairs of points.
-/
noncomputable def minLowMultiplicityDistances (n : ℕ) : ℕ :=
  sInf {(lowMultiplicityDistances P).ncard | (P : Finset ℝ²) (_ : P.card = n)}

/--
Let $A\subset \mathbb{R}^2$ be a set of $n$ points. Must there be two distances which occur at
least once but between at most $n$ pairs of points?

Note: we restrict to $n \geq 5$ following [Er84c]; the statement is false for $n = 4$, as
witnessed by two equilateral triangles of the same side-length glued together (see
`erdos_132.variants.four_points`).
-/
@[category research open, AMS 52]
theorem erdos_132.parts.i : answer(sorry) ↔ ∀ P : Finset ℝ², 5 ≤ P.card →
    2 ≤ (lowMultiplicityDistances P).ncard := by
  sorry

/--
Must the number of such distances (occurring at least once but between at most $n$ pairs of
points) $\to \infty$ as $n\to \infty$?
-/
@[category research open, AMS 52]
theorem erdos_132.parts.ii : answer(sorry) ↔
    Tendsto minLowMultiplicityDistances atTop atTop := by
  sorry

/--
Hopf and Pannwitz [HoPa34] proved that the largest distance between points of $A$ can occur at
most $n$ times.
-/
@[category research solved, AMS 52]
theorem erdos_132.variants.hopf_pannwitz (P : Finset ℝ²) (hP : P.Nonempty) :
    distanceMultiplicity P (Metric.diam (P : Set ℝ²)) ≤ P.card := by
  sorry

/--
By [HoPa34] the diameter always occurs at least once but at most $n$ times, so
`erdos_132.parts.i` is equivalent to asking whether a *second* such distance must occur:
besides the diameter, some other distance occurring at least once but between at most $n$
pairs of points.
-/
@[category research open, AMS 52]
theorem erdos_132.variants.second_distance : answer(sorry) ↔ ∀ P : Finset ℝ², 5 ≤ P.card →
    ∃ d ∈ lowMultiplicityDistances P, d ≠ Metric.diam (P : Set ℝ²) := by
  sorry

/--
The claim of `erdos_132.parts.i` is false for $n = 4$, as witnessed by two equilateral
triangles of the same side-length glued together: the common side-length occurs $5 > 4$ times
and the long diagonal is the only distance of multiplicity at most $4$.
-/
@[category research solved, AMS 52]
theorem erdos_132.variants.four_points :
    ∃ P : Finset ℝ², P.card = 4 ∧ (lowMultiplicityDistances P).ncard < 2 := by
  sorry

/--
Erdős and Fishburn [ErFi95] proved that there are at least two distances occurring at least
once but between at most $n$ pairs of points, for $n = 5$ and $n = 6$.
-/
@[category research solved, AMS 52]
theorem erdos_132.variants.erdos_fishburn (P : Finset ℝ²)
    (hP : P.card = 5 ∨ P.card = 6) :
    2 ≤ (lowMultiplicityDistances P).ncard := by
  sorry

/--
Clemen, Dumitrescu, and Liu [CDL25] have proved that there are always at least two such distances if $A$ is in convex position (that is, no point lies inside the convex hull of the others). They also prove it is true if the set $A$ is 'not too convex', in a specific technical sense.

[CDL25, Theorem 1.2] states this for all point sets in convex position with $n \geq 5$; the
hypothesis $n \geq 5$ is necessary, as the four-point configuration of
`erdos_132.variants.four_points` is in convex position.
-/
@[category research solved, AMS 52]
theorem erdos_132.variants.convex_position (P : Finset ℝ²) (hcard : 5 ≤ P.card)
    (hconv : ConvexIndep (P : Set ℝ²)) :
    2 ≤ (lowMultiplicityDistances P).ncard := by
  sorry

/--
It may be true that there are at least $n^{1-o(1)}$ many such distances. In [Er97e] Erdős offers \$100 for 'any nontrivial result'.
-/
@[category research open, AMS 52]
theorem erdos_132.variants.polynomial_count : answer(sorry) ↔
    ∃ E : ℕ → ℝ, E =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ n : ℕ, (n : ℝ) ^ (1 - E n) ≤ (minLowMultiplicityDistances n : ℝ) := by
  sorry

end Erdos132
