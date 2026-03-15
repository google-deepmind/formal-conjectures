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
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 506

*Reference:* [erdosproblems.com/506](https://www.erdosproblems.com/506)

What is the minimum number of circles determined by $n$ points in $\mathbb{R}^2$,
not all on a circle and not all on a line?

Related problems: [#104](https://www.erdosproblems.com/104),
[#831](https://www.erdosproblems.com/831).

[Er61] Erdős, P., _Some unsolved problems_, 1961, p. 245.

[El67] Elliott, P. D. T. A., _On the number of circles determined by $n$ points_,
Acta Mathematica Academiae Scientiarum Hungaricae (1967), 181–188.

[PuSm] Purdy, G. and Smith, J. W., _Lines, circles, and the number of determined circles_.

[BaBa94] Bálintová, A. and Bálint, V., _On the number of circles determined by $n$ points
in the Euclidean plane_, Acta Mathematica Hungarica (1994), 283–289.
-/

open Finset EuclideanGeometry

namespace Erdos506

/-- All points in $S$ lie on a common circle with positive radius. -/
noncomputable def AllOnCircle (S : Finset ℝ²) : Prop :=
  ∃ c : ℝ², ∃ r : ℝ, 0 < r ∧ ∀ p ∈ S, dist p c = r

/-- The number of distinct circles determined by $S$. A circle is identified by its
center and positive radius. It is "determined" by $S$ if at least $3$ points of $S$
lie on it. -/
noncomputable def numDeterminedCircles (S : Finset ℝ²) : ℕ :=
  Set.ncard {p : ℝ² × ℝ |
    0 < p.2 ∧ 3 ≤ Set.ncard {q ∈ (↑S : Set ℝ²) | dist q p.1 = p.2}}

/-- The minimum number of circles determined by any configuration of $n$ points in
$\mathbb{R}^2$ that are neither all on a circle nor all collinear. Returns $0$ when
no such configuration exists. -/
noncomputable def minDeterminedCircles (n : ℕ) : ℕ :=
  sInf (numDeterminedCircles '' {S : Finset ℝ² |
    S.card = n ∧ ¬AllOnCircle S ∧ ¬Collinear ℝ (↑S : Set ℝ²)})

/--
Erdős Problem 506 [Er61, p. 245]:

What is the minimum number of circles determined by $n$ points in $\mathbb{R}^2$, not all on a
circle (and not all on a line)?

Elliott [El67] proved that for $n > 393$ points not all on a circle or a line, the
points determine at least $\binom{n-1}{2}$ distinct circles. Purdy and Smith [PuSm]
corrected this to the sharper bound $\binom{n-1}{2} + 1 - \lfloor(n-1)/2\rfloor$, which is best
possible (witnessed by $n-1$ points on a circle and one point off it).
-/
@[category research solved, AMS 52]
theorem erdos_506 : ∀ n : ℕ, 393 < n →
    minDeterminedCircles n =
      answer(Nat.choose (n - 1) 2 + 1 - (n - 1) / 2) := by
  sorry

end Erdos506
