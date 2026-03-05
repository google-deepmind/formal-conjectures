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
# Erdős Problem 465

*Reference:* [erdosproblems.com/465](https://www.erdosproblems.com/465)

Let $N(X, \delta)$ denote the maximum number of points $P_1, \ldots, P_n$ which can be chosen
in a disk of radius $X$ in $\mathbb{R}^2$ such that $\|P_i - P_j\| \geq \delta$ for all
$1 \leq i < j \leq n$, where $\|x\|$ denotes the distance from $x$ to the nearest integer.

[Sa76] Sárközy, A., *On difference sets of sequences of integers. I.* Acta Math. Acad. Sci.
Hungar. 31 (1978), no. 1-2, 125-149.

[Ko01] Konyagin, S. V., *A remark on sets of numbers with large trigonometric sums.* 2001.
-/

namespace Erdos465

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt465 (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem 465, weak form (Proved by Sárközy [Sa76]):

For any $0 < \delta < 1/2$, $N(X, \delta) = o(X)$. Formalized as: for any $\varepsilon > 0$, for
sufficiently large $X$, any finite set of points in a closed disk of radius $X$
in $\mathbb{R}^2$ with all pairwise distances satisfying $\|d\| \geq \delta$ has at most
$\varepsilon \cdot X$ points.
-/
@[category research solved, AMS 11 52]
theorem erdos_465 (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
    ∀ (X : ℝ), X₀ ≤ X →
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ A, dist p 0 ≤ X) →
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt465 (dist p q) ≥ δ) →
      (A.card : ℝ) ≤ ε * X := by
  sorry

/--
Erdős Problem 465, strong form (Proved by Konyagin [Ko01]):

For any fixed $\delta > 0$, $N(X, \delta) \ll_\delta X^{1/2}$. Formalized as: there exists
$C > 0$ (depending on $\delta$) such that any finite set of points in a closed disk of radius
$X$ in $\mathbb{R}^2$ with all pairwise distances satisfying $\|d\| \geq \delta$ has at most
$C \cdot \sqrt{X}$ points.
-/
@[category research solved, AMS 11 52]
theorem erdos_465.variants.strong (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (X : ℝ), 0 < X →
    ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ A, dist p 0 ≤ X) →
      (∀ p ∈ A, ∀ q ∈ A, p ≠ q → distNearestInt465 (dist p q) ≥ δ) →
      (A.card : ℝ) ≤ C * Real.sqrt X := by
  sorry

end Erdos465
