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
# Erdős Problem 47

*Reference:* [erdosproblems.com/47](https://www.erdosproblems.com/47)

If $A \subseteq \{1, \ldots, N\}$ satisfies $\sum_{a \in A} 1/a > \delta \cdot \log N$ for some
$\delta > 0$ and $N$ sufficiently large, then $A$ contains a subset whose reciprocals sum to $1$.

Bloom [Bl21] proved that the weaker threshold
$\sum \frac{1}{n} \gg \frac{\log \log \log N}{\log \log N} \cdot \log N$ suffices,
which implies the conjecture below. Liu and Sawhney [LiSa24] further improved the threshold
to $(\log N)^{4/5 + o(1)}$.

Erdős conjectured that a threshold of $(\log \log N)^2$ might suffice; a construction by
Pomerance (discussed in [Bl21]) shows this would be optimal.

Related problems: 46, 298.

[Bl21] Bloom, T. F., _On a density conjecture about unit fractions_. arXiv:2112.03726 (2021).

[LiSa24] Liu, Y. and Sawhney, M., _On further questions regarding unit fractions_.
arXiv:2404.07113 (2024).
-/

open scoped BigOperators

namespace Erdos47

/--
If $\delta > 0$ and $N$ is sufficiently large (depending on $\delta$), and
$A \subseteq \{1, \ldots, N\}$ is such that
$$\sum_{a \in A} \frac{1}{a} > \delta \cdot \log N,$$
then there exists a nonempty subset $S \subseteq A$ such that
$$\sum_{n \in S} \frac{1}{n} = 1.$$

Proved by Bloom [Bl21], who showed the weaker threshold
$\sum \frac{1}{n} \gg \frac{\log \log \log N}{\log \log N} \cdot \log N$ suffices.
-/
@[category research solved, AMS 5 11]
theorem erdos_47 (δ : ℝ) (hδ : δ > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∑ a ∈ A, (1 : ℝ) / a) > δ * Real.log N →
      ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 := by
  sorry

/--
Bloom [Bl21] proved that if $A \subseteq \{1, \ldots, N\}$ satisfies
$$\sum_{a \in A} \frac{1}{a} \geq C \cdot \frac{\log \log \log N}{\log \log N} \cdot \log N$$
for some sufficiently large constant $C$, then $A$ contains a nonempty subset whose reciprocals
sum to $1$. This is strictly stronger than the $\delta \cdot \log N$ threshold in `erdos_47`.
-/
@[category research solved, AMS 5 11]
theorem erdos_47_bloom :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∑ a ∈ A, (1 : ℝ) / a) ≥
        C * (Real.log (Real.log (Real.log N)) / Real.log (Real.log N)) * Real.log N →
      ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 := by
  sorry

/--
Erdős conjectured that a threshold of $(\log \log N)^2$ should suffice: if
$A \subseteq \{1, \ldots, N\}$ satisfies $\sum_{a \in A} 1/a \geq (\log \log N)^2$,
then $A$ contains a nonempty subset whose reciprocals sum to $1$.
A construction by Pomerance shows this would be optimal.
-/
@[category research open, AMS 5 11]
theorem erdos_47_loglog_sq :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∑ a ∈ A, (1 : ℝ) / a) ≥ (Real.log (Real.log N)) ^ 2 →
      ∃ S : Finset ℕ, S.Nonempty ∧ S ⊆ A ∧ (∑ n ∈ S, (1 : ℝ) / n) = 1 := by
  sorry

end Erdos47
