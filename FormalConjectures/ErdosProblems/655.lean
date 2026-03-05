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
# Erdős Problem 655

Let $x_1, \ldots, x_n \in \mathbb{R}^2$ be such that no circle centered at one of the $x_i$
passes through three others. Are there at least $(1 + c) n / 2$ distinct distances for some
constant $c > 0$ and all $n$ sufficiently large?

*Reference:* [erdosproblems.com/655](https://www.erdosproblems.com/655)
-/

namespace Erdos655

/--
A finite set of points in $\mathbb{R}^2$ satisfies the "no three equidistant from a center"
condition if for each point $p$ in the set, no three other distinct points in the
set are equidistant from $p$ (i.e., no circle centered at $p$ passes through three
or more other points).
-/
def NoThreeEquidistantFromCenter (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q₁ ∈ P, ∀ q₂ ∈ P, ∀ q₃ ∈ P,
    p ≠ q₁ → p ≠ q₂ → p ≠ q₃ →
    q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
    ¬(dist p q₁ = dist p q₂ ∧ dist p q₂ = dist p q₃)

/--
The number of distinct pairwise distances determined by a finite point set in $\mathbb{R}^2$.
-/
noncomputable def distinctDistanceCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
Erdős Problem 655 (Erdős–Pach):
Let $x_1, \ldots, x_n \in \mathbb{R}^2$ be such that no circle whose centre is one of the $x_i$
contains three other points. Then the number of distinct distances determined
by the points is at least $(1 + c) \cdot n / 2$ for some constant $c > 0$ and all $n$
sufficiently large.
-/
@[category research open, AMS 52]
theorem erdos_655 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          NoThreeEquidistantFromCenter P →
          (distinctDistanceCount P : ℝ) ≥ (1 + c) * (n : ℝ) / 2 := by
  sorry

end Erdos655
