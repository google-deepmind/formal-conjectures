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
# Erdős Problem 466

*Reference:* [erdosproblems.com/466](https://www.erdosproblems.com/466)

Let $N(X, \delta)$ denote the maximum number of points $P_1, \ldots, P_n$ which can be chosen
in a disk of radius $X$ in $\mathbb{R}^2$ such that $\| |P_i - P_j| \| \geq \delta$ for all
$1 \leq i < j \leq n$, where $\|x\|$ denotes the distance from $x$ to the nearest integer.

This was proved by Graham, who showed $N(X, 1/10) > (\log X)/10$.
-/

namespace Erdos466

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem 466 (Proved by Graham):

There exists $\delta > 0$ such that $N(X, \delta) \to \infty$ as $X \to \infty$. Formalized as:
there exists $\delta > 0$ such that for every $M$, for sufficiently large $X$,
one can find at least $M$ points in a disk of radius $X$ in $\mathbb{R}^2$ whose
pairwise distances all satisfy $\|d\| \geq \delta$.
-/
@[category research solved, AMS 11 52]
theorem erdos_466 :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ M : ℕ, ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ (X : ℝ), X₀ ≤ X →
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      M ≤ A.card ∧
      (∀ p ∈ A, dist p 0 ≤ X) ∧
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt (dist p q) ≥ δ) := by
  sorry

end Erdos466
