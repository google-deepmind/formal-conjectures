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
# Erdős Problem 831

Estimate the function $h(n)$, where $h(n)$ is the minimum number of distinct circumradii
determined by $n$ points in $\mathbb{R}^2$ in general position (no three collinear, no four
concyclic).

*Reference:* [erdosproblems.com/831](https://www.erdosproblems.com/831)
-/

namespace Erdos831

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
The number of distinct circumradii of circles passing through three points of $P$.
A radius $r$ is counted if there exist three distinct points $a, b, c \in P$ and a
center $o$ such that all three points lie on the circle of radius $r$ centered at $o$.
-/
noncomputable def distinctCircumradiiCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {r : ℝ | r > 0 ∧ ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ∃ o : EuclideanSpace ℝ (Fin 2), dist a o = r ∧ dist b o = r ∧ dist c o = r}

/--
Let $h(n)$ be maximal such that in any $n$ points in $\mathbb{R}^2$ (with no three on a line
and no four on a circle) there are at least $h(n)$ many circles of different radii
passing through three points. Estimate $h(n)$.

Formalized as: $h(n) \to \infty$, i.e., for every $C$ there exists $N$ such that for all
$n \geq N$ and every set $P$ of $n$ points in $\mathbb{R}^2$ in general position (no three collinear,
no four concyclic), the number of distinct circumradii of circles through three
points is at least $C$.
-/
@[category research open, AMS 5 52]
theorem erdos_831 :
  ∀ C : ℕ,
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoThreeCollinear P →
        NoFourConcyclic P →
        distinctCircumradiiCount P ≥ C := by
  sorry

end Erdos831
