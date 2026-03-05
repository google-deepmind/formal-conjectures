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
# Erdős Problem 866

*Reference:* [erdosproblems.com/866](https://www.erdosproblems.com/866)

Let $k \geq 3$ and let $g_k(N)$ be minimal such that if $A \subseteq \{1, \ldots, 2N\}$ has
$|A| \geq N + g_k(N)$ then there exist integers $b_1, \ldots, b_k$ such that all $\binom{k}{2}$
pairwise sums $b_i + b_j$ are in $A$ (but the $b_i$ themselves need not be in $A$).

Estimate $g_k(N)$.

Known results:
- $g_3(N) = 2$ and $g_4(N) \leq 2032$
- $g_5(N) \asymp \log N$ and $g_6(N) \asymp N^{1/2}$
- $g_k(N) \ll_k N^{1 - 2^{-k}}$ for all $k \geq 3$
- For every $\varepsilon > 0$, if $k$ is sufficiently large then $g_k(N) > N^{1-\varepsilon}$

[CES75] Choi, S. L. G., Erdős, P., and Szemerédi, E., _Some additive and multiplicative
problems in combinatorics_, 1975.
-/

namespace Erdos866

/-- A finset $A$ of integers contains all pairwise sums of some $k$ integers: there exist
$b_1, \ldots, b_k \in \mathbb{Z}$ such that $b_i + b_j \in A$ for all $i < j$. -/
def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, ∀ i j : Fin k, i < j → (b i + b j) ∈ A

/-- $g_k(N)$ is the minimal $g \in \mathbb{N}$ such that every $A \subseteq \{1, \ldots, 2N\}$
with $|A| \geq N + g$ contains all pairwise sums of some $k$ integers. -/
noncomputable def gPairwiseSum (k N : ℕ) : ℕ :=
  sInf {g : ℕ | ∀ A : Finset ℤ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ 2 * (N : ℤ)) →
    A.card ≥ N + g → HasPairwiseSums A k}

/--
Erdős Problem 866, upper bound [CES75]:
For every $k \geq 3$, $g_k(N) \ll_k N^{1 - 2^{-k}}$, i.e., there exists a constant $C > 0$
(depending on $k$) such that $g_k(N) \leq C \cdot N^{1 - 1/2^k}$ for all $N \geq 1$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866 (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (gPairwiseSum k N : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) - 1 / (2 : ℝ) ^ k) := by
  sorry

/--
Erdős Problem 866 [CES75]: $g_3(N) = 2$ for all sufficiently large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.g3 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → gPairwiseSum 3 N = 2 := by
  sorry

/--
Erdős Problem 866, lower bound for large $k$ [CES75]:
For every $\varepsilon > 0$, there exists $k_0$ such that for all $k \geq k_0$,
$g_k(N) > N^{1 - \varepsilon}$ for all sufficiently large $N$.
-/
@[category research solved, AMS 5 11]
theorem erdos_866.variants.lower_bound_large_k :
    ∀ ε : ℝ, ε > 0 →
    ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (gPairwiseSum k N : ℝ) > (N : ℝ) ^ ((1 : ℝ) - ε) := by
  sorry

end Erdos866
