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
-/

namespace Erdos98

/--
A finite point set in $\mathbb{R}^2$ has no three collinear if every three-element subset
is not collinear (i.e., no line contains three or more of the points).
-/
def NoThreeCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
Four points in $\mathbb{R}^2$ are concyclic if they all lie on a common circle, i.e.,
there exists a center and positive radius such that all four points are
equidistant from the center.
-/
def FourPointsConcyclic (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, r > 0 ∧ ∀ p ∈ S, dist p c = r

/--
A finite point set in $\mathbb{R}^2$ has no four concyclic if every four-element subset
does not lie on a common circle.
-/
def NoFourConcyclic (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 4 → ¬FourPointsConcyclic S

/--
The number of distinct pairwise distances determined by a finite point set in $\mathbb{R}^2$.
-/
noncomputable def distinctDistanceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ dist p q = d}

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
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          NoThreeCollinear P →
          NoFourConcyclic P →
          (distinctDistanceCount P : ℝ) ≥ C * (n : ℝ) := by
  sorry

end Erdos98
