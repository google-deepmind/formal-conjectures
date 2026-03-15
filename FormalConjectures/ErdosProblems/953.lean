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
# Erdős Problem 953

*Reference:* [erdosproblems.com/953](https://www.erdosproblems.com/953)

Let $A \subset \{x \in \mathbb{R}^2 : |x| < r\}$ be a measurable set with no integer distances,
that is, such that $|a - b| \notin \mathbb{Z}$ for any distinct $a, b \in A$. How large can the
measure of $A$ be?

A problem of Erdős and Sárközy. The trivial upper bound is $O(r)$. Koizumi and
Kovac observed that Sárközy's lower bound from [466] can be adapted to give a
lower bound of $\gg_\varepsilon r^{1/2-\varepsilon}$ for all $\varepsilon > 0$.

See also [465] for a similar problem (concerning upper bounds) and [466] for a
similar problem (concerning lower bounds).

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._. Number Theory Day
(Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.
-/

open MeasureTheory

namespace Erdos953

/-- A set in $\mathbb{R}^2$ has no integer distances if for every pair of distinct points
$a, b$ in the set, the Euclidean distance $|a - b|$ is not an integer. -/
def NoIntegerDistances (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ∀ n : ℤ, dist a b ≠ ↑n

/-- The supremum of the Lebesgue measure of measurable subsets of $B(0, r)$ in $\mathbb{R}^2$
with no integer distances. -/
noncomputable def maxNoIntDistMeasure (r : ℝ) : ℝ :=
  sSup ((fun A => (volume A).toReal) ''
    {A : Set (EuclideanSpace ℝ (Fin 2)) | MeasurableSet A ∧
      A ⊆ Metric.ball 0 r ∧
      NoIntegerDistances A})

/--
Erdős Problem 953 [Er77c]: How large can the Lebesgue measure of a measurable set
$A \subset B(0, r) \subset \mathbb{R}^2$ with no integer distances be?
The trivial upper bound is $O(r)$ and a lower bound of
$\gg_\varepsilon r^{1/2-\varepsilon}$ is known.
-/
@[category research open, AMS 28 52]
theorem erdos_953 :
    ∀ (r : ℝ), 0 < r →
    maxNoIntDistMeasure r = (answer(sorry) : ℝ → ℝ) r := by
  sorry

/--
Erdős Problem 953 — trivial upper bound:
The Lebesgue measure of any measurable set $A \subset B(0, r)$ in $\mathbb{R}^2$ with no integer
distances is $O(r)$. That is, there exists an absolute constant $C > 0$ such that
for all $r > 0$ and all such $A$, $\mu(A) \leq C \cdot r$.
-/
@[category research solved, AMS 28 52]
theorem erdos_953.variants.upper :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r : ℝ), 0 < r →
    ∀ (A : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet A →
      A ⊆ Metric.ball 0 r →
      NoIntegerDistances A →
      (volume A).toReal ≤ C * r := by
  sorry

/--
Erdős Problem 953 — lower bound:
For every $\varepsilon > 0$, there exists $c > 0$ such that for all sufficiently large $r$,
there exists a measurable set $A \subset B(0, r)$ in $\mathbb{R}^2$ with no integer distances
and $\mu(A) \geq c \cdot r^{1/2 - \varepsilon}$.
-/
@[category research solved, AMS 28 52]
theorem erdos_953.variants.lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
    ∃ r₀ : ℝ, 0 < r₀ ∧
    ∀ (r : ℝ), r₀ ≤ r →
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet A ∧
      A ⊆ Metric.ball 0 r ∧
      NoIntegerDistances A ∧
      (volume A).toReal ≥ c * r ^ ((1 : ℝ) / 2 - ε) := by
  sorry

end Erdos953
