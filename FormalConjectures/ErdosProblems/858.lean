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
# Erdős Problem 858

*Reference:* [erdosproblems.com/858](https://www.erdosproblems.com/858)

Let $A \subseteq \{1, \ldots, N\}$ be such that there is no solution to $at = b$ with
$a, b \in A$ and the smallest prime factor of $t$ is $> a$. Estimate the maximum of
$$\frac{1}{\log N} \sum_{n \in A} \frac{1}{n}.$$

Alexander [Al66] and Erdős, Sárközi, and Szemerédi [ESS68] proved that this
maximum is $o(1)$ (as $N \to \infty$). This condition on $A$ is a weaker form of the
usual primitive condition. If $A$ is primitive then Behrend [Be35] proved
$$\frac{1}{\log N} \sum_{n \in A} \frac{1}{n} \ll \frac{1}{\sqrt{\log \log N}}.$$

An example of such a set $A$ is the set of all integers in $[N^{1/2}, N]$
divisible by some prime $> N^{1/2}$.

[Al66] Alexander, R., *Density and sequence of subsets of integers*.

[ESS68] Erdős, P., Sárközi, A., and Szemerédi, E., *On divisibility properties of
sequences of integers*.

[Be35] Behrend, F., *On sequences of numbers not divisible one by another*.
J. London Math. Soc. **10** (1935), 42-44.
-/

open scoped BigOperators

namespace Erdos858

/-- A finite set $A$ of positive integers satisfies the *weak primitive* condition
if whenever $at = b$ for $a, b \in A$ with $t > 1$, the smallest prime factor of $t$
is at most $a$. -/
def IsWeakPrimitive (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a < b → a ∣ b →
    Nat.minFac (b / a) ≤ a

/-- The maximum of $\sum_{n \in A} \frac{1}{n}$ over all weak-primitive subsets
$A \subseteq \{1, \ldots, N\}$. -/
noncomputable def weakPrimitiveMaxSum (N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    IsWeakPrimitive A ∧
    x = ∑ n ∈ A, (1 : ℝ) / (n : ℝ)}

/--
**Erdős Problem 858** — Known result [Al66, ESS68]:

The quantity $\frac{1}{\log N} \cdot \max\left\{\sum_{n \in A} \frac{1}{n}\right\}$ over
weak-primitive subsets $A \subseteq \{1, \ldots, N\}$ tends to $0$ as $N \to \infty$.

Formulated as: for every $\varepsilon > 0$, there exists $N_0$ such that for all $N \geq N_0$,
$\mathrm{weakPrimitiveMaxSum}(N) \leq \varepsilon \cdot \log N$.
-/
@[category research solved, AMS 11]
theorem erdos_858 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      weakPrimitiveMaxSum N ≤ ε * Real.log (N : ℝ) := by
  sorry

/--
**Erdős Problem 858** — Behrend-type conjecture:

Does there exist $C > 0$ such that for all sufficiently large $N$,
$$\frac{1}{\log N} \cdot \max\left\{\sum_{n \in A} \frac{1}{n}\right\}
  \leq \frac{C}{\sqrt{\log \log N}}?$$
-/
@[category research open, AMS 11]
theorem erdos_858.variants.behrend_type :
    answer(sorry) ↔
    (∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      weakPrimitiveMaxSum N ≤ C * Real.log (N : ℝ) /
        Real.sqrt (Real.log (Real.log (N : ℝ)))) := by
  sorry

end Erdos858
