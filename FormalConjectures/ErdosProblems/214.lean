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
# Erdős Problem 214

Let $S \subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart.
Must the complement of $S$ contain four points which form a unit square?

*Reference:* [erdosproblems.com/214](https://www.erdosproblems.com/214)

[Er83c] Erdős, P., _Old and new problems in combinatorial analysis and graph theory_, 1983.

[Ju79] Juhász, R., _Ramsey type theorems in the plane_. Journal of Combinatorial Theory, Series A
**27** (1979), 152–160.
-/

namespace Erdos214

/--
Four points in $\mathbb{R}^2$ form a "unit square" if, when taken in cyclic order
$a \to b \to c \to d$, all four sides have length $1$ and both diagonals have length $\sqrt{2}$.
The four points must also be pairwise distinct.
-/
def IsUnitSquare (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1 ∧
  dist a c = Real.sqrt 2 ∧ dist b d = Real.sqrt 2

/--
Let $S \subset \mathbb{R}^2$ be such that no two points in $S$ are distance $1$ apart.
Then the complement of $S$ must contain four points which form a unit square.

This was proved by Juhász [Ju79], who showed more generally that the complement of $S$
must contain a congruent copy of any set of four points.
-/
@[category research solved, AMS 52]
theorem erdos_214 :
    ∀ (S : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ S, ∀ q ∈ S, dist p q ≠ 1) →
      ∃ a b c d : EuclideanSpace ℝ (Fin 2),
        a ∈ Sᶜ ∧ b ∈ Sᶜ ∧ c ∈ Sᶜ ∧ d ∈ Sᶜ ∧
        IsUnitSquare a b c d := by
  sorry

/--
Juhász's general theorem: if $S \subset \mathbb{R}^2$ is such that no two points in $S$ are
distance $1$ apart, then for any set of four points $P$, the complement of $S$ contains a
congruent copy of $P$. This is strictly stronger than `erdos_214`, which only asserts the
existence of a unit square in the complement.
-/
@[category research solved, AMS 52]
theorem erdos_214_general :
    ∀ (S : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ S, ∀ q ∈ S, dist p q ≠ 1) →
      ∀ (P : Fin 4 → EuclideanSpace ℝ (Fin 2)),
        ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
          Isometry f ∧ ∀ i, f (P i) ∈ Sᶜ := by
  sorry

/--
Does Juhász's result extend to five-point configurations? That is, if $S \subset \mathbb{R}^2$
has no two points at unit distance, must the complement of $S$ contain a congruent copy of
every set of five points? This remains open.
-/
@[category research open, AMS 52]
theorem erdos_214_five_points :
    ∀ (S : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ S, ∀ q ∈ S, dist p q ≠ 1) →
      ∀ (P : Fin 5 → EuclideanSpace ℝ (Fin 2)),
        ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
          Isometry f ∧ ∀ i, f (P i) ∈ Sᶜ := by
  sorry

end Erdos214
