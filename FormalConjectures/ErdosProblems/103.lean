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

*Reference:* [erdosproblems.com/103](https://www.erdosproblems.com/103)

Let $h(n)$ count the number of incongruent $n$-point configurations in $\mathbb{R}^2$ that
minimize the diameter subject to all pairwise distances being $\geq 1$. Does $h(n) \to \infty$?
-/

namespace Erdos103

/--
A finite set of points in $\mathbb{R}^2$ is unit-separated if all pairwise distances
between distinct points are at least $1$.
-/
def IsUnitSeparated (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ≠ q → dist p q ≥ 1

/--
The diameter of a finite set of points in $\mathbb{R}^2$: the supremum of all pairwise distances.
-/
noncomputable def finiteDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sSup {d : ℝ | ∃ p ∈ A, ∃ q ∈ A, d = dist p q}

/--
A configuration of $n$ points in $\mathbb{R}^2$ minimizes the diameter among all unit-separated
$n$-point configurations: it is unit-separated, and no other unit-separated $n$-point set
has strictly smaller diameter.
-/
def IsMinimalDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  IsUnitSeparated A ∧
  ∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
    B.card = A.card → IsUnitSeparated B → finiteDiameter A ≤ finiteDiameter B

/--
Two finite point sets in $\mathbb{R}^2$ are congruent if there is an isometric equivalence of
$\mathbb{R}^2$ mapping one to the other (i.e., one can be obtained from the other by a
rigid motion).
-/
def AreCongruent (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
    A.image (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) = B

/--
$h(n)$ counts the number of congruence classes of minimal-diameter unit-separated
$n$-point configurations in $\mathbb{R}^2$. That is, it counts the number of incongruent sets
of $n$ points that minimize the diameter subject to $d(x,y) \geq 1$ for all $x \neq y$.
-/
noncomputable def h (n : ℕ) : ℕ :=
  let minimizers : Set (Finset (EuclideanSpace ℝ (Fin 2))) :=
    {A | A.card = n ∧ IsMinimalDiameter A}
  Set.ncard {C : Set (Finset (EuclideanSpace ℝ (Fin 2))) |
    ∃ A ∈ minimizers, C = minimizers ∩ {B | AreCongruent A B}}

/--
Erdős Problem #103:
Let $h(n)$ count the number of incongruent sets of $n$ points in $\mathbb{R}^2$ which minimize
the diameter subject to the constraint that $d(x,y) \geq 1$ for all distinct points
$x$, $y$. Is it true that $h(n) \to \infty$ as $n \to \infty$?

It is not even known whether $h(n) \geq 2$ for all sufficiently large $n$.
-/
@[category research open, AMS 52]
theorem erdos_103 : answer(sorry) ↔ ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → h n ≥ M := by
  sorry

end Erdos103
