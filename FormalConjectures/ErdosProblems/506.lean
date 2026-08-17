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
# Erdős Problem 506

*References:*
- [erdosproblems.com/506](https://www.erdosproblems.com/506)
- [El67] Elliott, P. D. T. A., *On the number of circles determined by $n$ points*, Acta Math.
  Acad. Sci. Hungar. (1967), 181–188.
- [BaBa94] Bálintová, A. and Bálint, V., *On the number of circles determined by $n$ points in the
  Euclidean plane*, Acta Math. Hungar. (1994), 283–289.
- [PuSm] Purdy and Smith. No reference found.
-/

namespace Erdos506

open EuclideanGeometry

/--
The number of circles determined by a set of points `P` in the plane: the number of distinct
circles (spheres) passing through at least three of the points of `P`. (Three distinct points lie
on a common circle precisely when they are not collinear, so this counts exactly the circumcircles
of the non-collinear triples of `P`.)
-/
noncomputable def numCircles (P : Set ℝ²) : ℕ :=
  Set.ncard { s : Sphere ℝ² | 3 ≤ {p ∈ P | p ∈ s}.ncard }

/--
What is the minimum number of circles determined by any $n$ points in $\mathbb{R}^2$, not all on a
circle?

There is clearly some non-degeneracy condition intended here - probably either that not all the
points are on a line, or the stronger condition that no three points are on a line.

The answer is known for $n > 393$ (see `erdos_506.variants.large_n`) but the problem appears to
remain open for small $n$ (see `erdos_506.variants.small_n`).
-/
-- Formalisation notes:
-- * Following Elliott, the non-degeneracy condition used here is the weaker of the two: the points
--   are not all on a line and not all on a circle.
-- * The hypothesis `4 ≤ n` is not a restriction of the problem, but excludes the degenerate range
--   where no admissible configuration exists: fewer than three points are collinear, and any three
--   non-collinear points lie on a common circle, so the set below is empty for `n < 4`.
@[category research open, AMS 51 52]
theorem erdos_506 (n : ℕ) (hn : 4 ≤ n) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      answer(sorry) := by
  sorry

/--
For $n > 393$ the answer is $\binom{n-1}{2} + 1 - \left\lfloor \frac{n-1}{2} \right\rfloor$
(Elliott [El67], with the correction of Purdy and Smith [PuSm], also reported in [BaBa94]): this is
both a lower bound for every such configuration and is attained, e.g. by a circle with $n - 1$
points together with a single point off the circle.
-/
@[category research solved, AMS 51 52]
theorem erdos_506.variants.large_n (n : ℕ) (hn : 393 < n) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      answer((n - 1).choose 2 + 1 - (n - 1) / 2) := by
  sorry

/--
The problem appears to remain open for small $n$: Elliott's answer is established only for
$n > 393$, so the minimum number of circles determined by $n$ points, not all on a line and not all
on a circle, is unknown for $n \le 393$.
-/
@[category research open, AMS 51 52]
theorem erdos_506.variants.small_n (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 393) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      answer(sorry) := by
  sorry

/--
Segre's observation: the lower bound $\binom{n-1}{2}$ (without the correction of [PuSm]) is
already false for $n = 8$, as witnessed by the projection of a cube onto a plane. Hence the minimum
number of circles determined by $8$ such points is strictly less than $\binom{7}{2} = 21$.
-/
@[category research solved, AMS 51 52]
theorem erdos_506.variants.segre_n_eq_eight :
    ∃ P : Finset ℝ²,
      P.card = 8 ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
      numCircles (P : Set ℝ²) < (8 - 1).choose 2 := by
  sorry

end Erdos506
