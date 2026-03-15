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
# Erdős Problem 98

*Reference:* [erdosproblems.com/98](https://www.erdosproblems.com/98)

Let $h(n)$ be the minimum number of distinct distances determined by $n$ points in
$\mathbb{R}^2$ with no three collinear and no four concyclic. Does $h(n)/n \to \infty$?

[Er75f] Erdős, P., _Problems and results in combinatorial geometry_, 1975, p. 101.

[Er83c] Erdős, P., _Old and new problems in combinatorial analysis and graph theory_, 1983.

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive geometry
(Siófok, 1985) (1987), 167-177.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
467-478.

[Er92b] Erdős, P., _Some of my old and new problems in elementary number theory and
geometry_. Proceedings of the Fifth Canadian Number Theory Association Conference (1992).

[EFPR93] Erdős, P., Füredi, Z., Pach, J., and Ruzsa, I. Z., _The grid revisited_.
Discrete Mathematics (1993), 189-196.

[Er94b] Erdős, P., _Some old and new problems in various branches of combinatorics_.
Discrete Math. 165/166 (1997), 227-231.

[Er97e] Erdős, P., _Some problems and results on combinatorial number theory_ (1997).
-/

open EuclideanGeometry

namespace Erdos98

/--
A finite point set in $\mathbb{R}^2$ has no three collinear if every three-element subset
is not collinear (i.e., no line contains three or more of the points).
-/
def NoThreeCollinear (P : Finset (ℝ²)) : Prop :=
  ∀ S : Finset (ℝ²),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (ℝ²))

/--
Four points in $\mathbb{R}^2$ are concyclic if they all lie on a common circle, i.e.,
there exists a center and positive radius such that all four points are
equidistant from the center.
-/
def FourPointsConcyclic (S : Finset (ℝ²)) : Prop :=
  ∃ c : ℝ², ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, dist p c = r

/--
A finite point set in $\mathbb{R}^2$ has no four concyclic if every four-element subset
does not lie on a common circle.
-/
def NoFourConcyclic (P : Finset (ℝ²)) : Prop :=
  ∀ S : Finset (ℝ²),
    S ⊆ P → S.card = 4 → ¬FourPointsConcyclic S

/--
Erdős Problem 98:
Let $h(n)$ be the minimum number of distinct distances determined by any $n$ points
in $\mathbb{R}^2$ with no three collinear and no four concyclic. Does $h(n)/n \to \infty$?

Formally: for every $C > 0$ there exists $N$ such that for all $n \geq N$ and every
set $P$ of $n$ points in $\mathbb{R}^2$ with no three collinear and no four concyclic,
the number of distinct distances is at least $C \cdot n$.
-/
@[category research open, AMS 5 52]
theorem erdos_98 : answer(sorry) ↔
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset ℝ²,
          P.card = n →
          NoThreeCollinear P →
          NoFourConcyclic P →
          (distinctDistances P : ℝ) ≥ C * (n : ℝ) := by
  sorry

end Erdos98
