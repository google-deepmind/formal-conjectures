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

[Ju79] Juhász, R., _Ramsey type theorems in the plane_, 1979.
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

end Erdos214
