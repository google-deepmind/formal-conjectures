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
# Erdős Problem 232

*Reference:* [erdosproblems.com/232](https://www.erdosproblems.com/232)

For $A \subseteq \mathbb{R}^2$ we define the upper density as
$$\bar{\delta}(A) = \limsup_{R\to\infty} \frac{\lambda(A \cap B_R)}{\lambda(B_R)},$$
where $\lambda$ is the Lebesgue measure and $B_R$ is the ball of radius $R$.

Estimate $m_1 = \sup \bar{\delta}(A)$, where $A$ ranges over all measurable subsets of
$\mathbb{R}^2$ without two points distance $1$ apart. In particular, is $m_1 \le 1/4$?

Originally a question of Moser [Mo66]. The trivial upper bound is $m_1 \le 1/2$,
since for any unit vector $u$ the sets $A$ and $A + u$ must be disjoint.
A lower bound of $m_1 \ge \pi/(8\sqrt{3}) \approx 0.2267$ comes from the union of open
circular discs of radius $1/2$ at a regular hexagonal lattice.

Proved by Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23],
who showed $m_1 \le 0.247 < 1/4$.

[Mo66] Moser, L., *Problem 10*, Canad. Math. Bull. 9 (1966).

[Er85] Erdős, P., *Problems and results in combinatorial geometry*, 1985, p. 4.

[ACMVZ23] Ambrus, G., Csiszárik, A., Matolcsi, M., Varga, D., and Zsámboki, P.,
*The density of planar sets avoiding unit distances*, 2023.
-/

open MeasureTheory Metric

namespace Erdos232

/-- A set in a metric space is *unit-distance-free* if no two points in the set
are exactly distance $1$ apart. -/
def IsUnitDistanceFree {X : Type*} [PseudoMetricSpace X] (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≠ 1

/--
Erdős Problem 232 [Er85, p.4] (PROVED):

For every measurable unit-distance-free set $A \subseteq \mathbb{R}^2$, the upper density
$$\limsup_{R\to\infty} \frac{\lambda(A \cap B_R)}{\lambda(B_R)} \le \frac{1}{4}.$$

Formalized as: for every $\varepsilon > 0$, for all sufficiently large $R$, the density
ratio $\lambda(A \cap B_R) / \lambda(B_R) \le 1/4 + \varepsilon$. This is equivalent to the
$\limsup$ being at most $1/4$.

Proved by Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki [ACMVZ23] who showed
the stronger bound $m_1 \le 0.247$.
-/
@[category research solved, AMS 28 52]
theorem erdos_232 : answer(True) ↔
    ∀ (A : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet A → IsUnitDistanceFree A →
      ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
          (volume (A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)).toReal /
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)).toReal ≤ 1 / 4 + ε := by
  sorry

end Erdos232
