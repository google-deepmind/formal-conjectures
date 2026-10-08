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
# Erdős Problem 654

*References:*
- [erdosproblems.com/654](https://www.erdosproblems.com/654)
- [Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*. Intuitive geometry
  (Siófok, 1985) (1987), 167-177.
- [ErPa90] Erdős, P. and Pach, J., *Variations on the theme of repeated distances*.
  Combinatorica (1990), 261--269.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Fe26] T. Feng et al, *Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
  Erdős Problems*. arXiv:2601.22401 (2026).
-/

@[expose] public section

open Filter Finset EuclideanGeometry

namespace Erdos654

/-- `NoFourConcyclic A` means that no four distinct points of $A$ lie on a common circle.

In the plane, `Cospherical` means lying on a common circle. Four distinct collinear points are
never cospherical, so collinear points are allowed. Stated for `Set ℝ²`; a `Finset` argument
coerces. -/
def NoFourConcyclic (A : Set ℝ²) : Prop :=
  ∀ T ⊆ A, T.ncard = 4 → ¬Cospherical T

/--
Let $f(n)$ be such that, given any $x_1,\ldots,x_n\in \mathbb{R}^2$ with no four points on a
circle, there exists some $x_i$ with at least $f(n)$ many distinct distances to the other $x_j$.
Is it true that $f(n) > (1-o(1))n$?

Erdős asks this in [Er97e]. The answer is no: Aletheia [Fe26] constructed, for every $m \geq 10$,
a set of $n = 4m$ points with no four on a circle such that every point has fewer than
$\frac{3}{4}n$ distinct distances to the other points. This gives infinitely many $n$, which is
enough to refute the statement with $\varepsilon = 1/8$. See `Erdos654.erdos_654.variants.feng`.
-/
@[category research solved, AMS 52]
theorem erdos_654.parts.i : answer(False) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

/--
Let $f(n)$ be as in `erdos_654.parts.i`. Is it true that $f(n) > (\frac{1}{3}+c)n$ for some
constant $c>0$ and all large $n$?
-/
@[category research open, AMS 52]
theorem erdos_654.parts.ii : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → NoFourConcyclic A →
      ∃ x ∈ A, (1 / 3 + c) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

/--
It is trivial that $f(n) \geq \frac{n-1}{3}$.

In fact every point $x$ has at least $\frac{n-1}{3}$ distinct distances to the other points: a
circle centred at $x$ contains at most three other points, since four would lie on a common
circle.
-/
@[category textbook, AMS 52]
theorem erdos_654.variants.trivial_bound (A : Finset ℝ²) (hA : NoFourConcyclic A) :
    ∀ x ∈ A, ((#A : ℝ) - 1) / 3 ≤ (distinctDistancesFrom A x : ℝ) := by
  sorry

/--
Aletheia [Fe26] showed that for every $m \geq 10$ there is a set of $n = 4m$ points in
$\mathbb{R}^2$, no four on a circle, such that every point has fewer than $\frac{3}{4}n = 3m$
distinct distances to the other points.

The construction places $2m$ points on each of two perpendicular lines, so it is not in general
position. Each point has at most $3m - 1$ distinct distances to the other points.
-/
@[category research solved, AMS 52]
theorem erdos_654.variants.feng (m : ℕ) (hm : 10 ≤ m) :
    ∃ A : Finset ℝ², #A = 4 * m ∧ NoFourConcyclic A ∧
      ∀ x ∈ A, distinctDistancesFrom A x < 3 * m := by
  sorry

/--
Erdős [Er87b] and Erdős and Pach [ErPa90] ask the question of `erdos_654.parts.ii` under the
additional assumption that no three points are on a line. Let $x_1,\ldots,x_n\in \mathbb{R}^2$ with
no three points on a line and no four points on a circle. Is there some $x_i$ with at least
$(\frac{1}{3}+c)n$ distinct distances to the other $x_j$, for some constant $c>0$ and all large
$n$?
-/
@[category research open, AMS 52]
theorem erdos_654.variants.general_position : answer(sorry) ↔
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → InGeneralPosition A →
      ∃ x ∈ A, (1 / 3 + c) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

/--
Let $x_1,\ldots,x_n\in \mathbb{R}^2$ with no three points on a line and no four points on a
circle. Is there some $x_i$ with at least $(1-o(1))n$ distinct distances to the other $x_j$?

This is the general-position analogue of `Erdos654.erdos_654.parts.i`. The remark on
erdosproblems.com notes that the construction of [Fe26], which has all points on two lines, does
not settle the version in general position.
-/
@[category research open, AMS 52]
theorem erdos_654.variants.general_position_one_sub_eps : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → InGeneralPosition A →
      ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

/-- `AtMostTwoPerCircle A` means that every circle centred at a point $x \in A$ contains at most
two other points of $A$. -/
def AtMostTwoPerCircle (A : Finset ℝ²) : Prop :=
  ∀ x ∈ A, ∀ r : ℝ, #((A.erase x).filter fun y ↦ dist y x = r) ≤ 2

/--
Erdős and Pach [ErPa90] suggest that the bound $(1-o(1))n$ holds under the assumption that every
circle centred at a point $x_i$ contains at most $2$ other points $x_j$. We state this for points
in general position (no three on a line and no four on a circle [Er87b, p. 167]), the setting in
which [Er87b] and [ErPa90] ask the weaker question. Without the assumption of no three points on a
line the statement is false: the sets of [Fe26] satisfy the circle condition.
-/
@[category research open, AMS 52]
theorem erdos_654.variants.erdos_pach : answer(sorry) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², #A = n → InGeneralPosition A →
      AtMostTwoPerCircle A → ∃ x ∈ A, (1 - ε) * (n : ℝ) < (distinctDistancesFrom A x : ℝ) := by
  sorry

end Erdos654
