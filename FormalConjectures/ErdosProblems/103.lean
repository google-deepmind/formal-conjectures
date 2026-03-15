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
# Erdős Problem 103

*References:*
* [erdosproblems.com/103](https://www.erdosproblems.com/103)
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial geometry_.
  Math. Pannon. (1994), 261–269.

Related: Problem #99.

Let $h(n)$ count the number of incongruent $n$-point configurations in $\mathbb{R}^2$ that
minimize the diameter subject to all pairwise distances being $\geq 1$. Does $h(n) \to \infty$?
-/

open Set Metric

namespace Erdos103

/--
A finite set of points in $\mathbb{R}^2$ is unit-separated if all pairwise distances
between distinct points are at least $1$.
-/
def IsUnitSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1

/--
Two finite point sets in $\mathbb{R}^2$ are congruent if there is an isometric equivalence of
$\mathbb{R}^2$ mapping one to the other (i.e., one can be obtained from the other by a
rigid motion).
-/
def AreCongruent (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
    A.image (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = B

/--
Erdős Problem #103:
Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimize
the diameter subject to the constraint that $d(x,y) \geq 1$ for all distinct points
$x$, $y$. Is it true that $h(n) \to \infty$ as $n \to \infty$?

The formulation uses an existential quantification over $M$ pairwise non-congruent
minimal-diameter configurations, following the pattern of Problem 668, to avoid
the `Set.ncard` pitfall (which returns 0 for infinite sets).

It is not even known whether $h(n) \geq 2$ for all sufficiently large $n$.
-/
@[category research open, AMS 52]
theorem erdos_103 : answer(sorry) ↔
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (As : Fin M → Finset (EuclideanSpace ℝ (Fin 2))),
        (∀ i, (As i).card = n ∧ IsUnitSeparated (As i) ∧
          IsMinOn (fun B : Finset (EuclideanSpace ℝ (Fin 2)) =>
              diam (B : Set (EuclideanSpace ℝ (Fin 2))))
            {B | B.card = n ∧ IsUnitSeparated B} (As i)) ∧
        (∀ i j, i ≠ j → ¬AreCongruent (As i) (As j)) := by
  sorry

/--
Weaker variant of Erdős Problem #103: Are there at least two incongruent minimal-diameter
unit-separated $n$-point configurations for all sufficiently large $n$?
-/
@[category research open, AMS 52]
theorem erdos_103_at_least_two : answer(sorry) ↔
    ∀ᶠ n in Filter.atTop,
      ∃ (A B : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧ IsUnitSeparated A ∧
          IsMinOn (fun C : Finset (EuclideanSpace ℝ (Fin 2)) =>
              diam (C : Set (EuclideanSpace ℝ (Fin 2))))
            {C | C.card = n ∧ IsUnitSeparated C} A ∧
        B.card = n ∧ IsUnitSeparated B ∧
          IsMinOn (fun C : Finset (EuclideanSpace ℝ (Fin 2)) =>
              diam (C : Set (EuclideanSpace ℝ (Fin 2))))
            {C | C.card = n ∧ IsUnitSeparated C} B ∧
        ¬AreCongruent A B := by
  sorry

end Erdos103
