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
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 506

*References:*
- [erdosproblems.com/506](https://www.erdosproblems.com/506)
- [El67] Elliott, P. D. T. A., *On the number of circles determined by $n$ points*, Acta Math.
  Acad. Sci. Hungar. (1967), 181–188.
- [BaBa94] Bálintová, A. and Bálint, V., *On the number of circles determined by $n$ points in the
  Euclidean plane*, Acta Math. Hungar. (1994), 283–289.
- [PuSm] Purdy and Smith. No reference found.
- [Wang26] Liyan Wang, *Circles determined by planar point sets* (2026), Theorem 1.2.
  [arXiv:2608.19844](https://arxiv.org/abs/2608.19844)
-/

@[expose] public section

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

def erdos_506.answer (n : ℕ) : ℕ := sorry

/--
What is the minimum number of circles determined by any $n$ points in $\mathbb{R}^2$, not all on a
circle?

There is clearly some non-degeneracy condition intended here - probably either that not all the
points are on a line, or the stronger condition that no three points are on a line.

The cases $4 \le n \le 393$ and $n > 393$ are stated in `erdos_506.variants.small_n` and
`erdos_506.variants.large_n`, respectively.
-/
-- Formalisation notes:
-- * Following Elliott, the non-degeneracy condition used here is the weaker of the two: the points
--   are not all on a line and not all on a circle.
-- * The hypothesis `4 ≤ n` is not a restriction of the problem, but excludes the degenerate range
--   where no admissible configuration exists: fewer than three points are collinear, and any three
--   non-collinear points lie on a common circle, so the set below is empty for `n < 4`.
@[category research open, question value, AMS 51 52]
theorem erdos_506 (n : ℕ) (hn : 4 ≤ n) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      (erdos_506.answer n) := by
  sorry

def erdos_506.variants.large_n.answer (n : ℕ) : ℕ := (n - 1).choose 2 + 1 - (n - 1) / 2

/--
For $n > 393$ the answer is $\binom{n-1}{2} + 1 - \left\lfloor \frac{n-1}{2} \right\rfloor$
(Elliott [El67], with the correction of Purdy and Smith [PuSm], also reported in [BaBa94]): this is
both a lower bound for every such configuration and is attained, e.g. by a circle with $n - 1$
points together with a single point off the circle.
-/
@[category research solved, question value, AMS 51 52]
theorem erdos_506.variants.large_n (n : ℕ) (hn : 393 < n) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      (erdos_506.variants.large_n.answer n) := by
  sorry

def erdos_506.variants.small_n.answer (n : ℕ) : ℕ :=
  if n = 6 then 8
  else if n = 7 then 11
  else if n = 8 then 17
  else erdos_506.variants.large_n.answer n

set_option linter.style.formal_proof_palomar false in
/--
For $4 \le n \le 393$, the minimum number of circles is $8$, $11$, and $17$ at $n=6,7,8$,
respectively. At every other order in this range it is
$\binom{n-1}{2}+1-\lfloor(n-1)/2\rfloor$ [Wang26, Theorem 1.2].
-/
@[category research solved, question value, AMS 51 52, formal_proof using lean4 at
  "https://github.com/rafalwronapl/erdos506-review-package-2026-08-16/blob/f647646e77e48c10cf7928d5203214b520537506/formalization/Erdos506/Canonical.lean#L233"]
theorem erdos_506.variants.small_n (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 393) :
    IsLeast { k : ℕ | ∃ P : Finset ℝ²,
        P.card = n ∧ ¬ Collinear ℝ (P : Set ℝ²) ∧ ¬ Cospherical (P : Set ℝ²) ∧
        numCircles (P : Set ℝ²) = k }
      (erdos_506.variants.small_n.answer n) := by
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
