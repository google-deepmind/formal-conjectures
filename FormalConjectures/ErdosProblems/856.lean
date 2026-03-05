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
# Erdős Problem 856

*Reference:* [erdosproblems.com/856](https://www.erdosproblems.com/856)

Let $k \geq 3$ and $f_k(N)$ be the maximum value of $\sum_{n \in A} 1/n$, where $A$
ranges over all subsets of $\{1, \ldots, N\}$ which contain no subset of size $k$
with the same pairwise least common multiple.

Estimate $f_k(N)$.

[Er70] Erdős, P. (1970)

[TaZh25b] Tang, R. and Zhang, R. (2025)
-/

open Finset Real

namespace Erdos856

/-- A finite set of natural numbers has no $k$-element subset where all pairwise
LCMs are equal. That is, there is no $S \subseteq A$ with $|S| = k$ and a value $L$
such that $\operatorname{lcm}(a, b) = L$ for all distinct $a, b \in S$. -/
def NoPairwiseLcmClique (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = k →
    ¬∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- $f_k(N)$: the supremum of $\sum_{n \in A} 1/n$ over subsets $A \subseteq \{1, \ldots, N\}$
with no $k$-element subset having all pairwise LCMs equal. -/
noncomputable def fk (k N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    NoPairwiseLcmClique A k ∧
    x = ∑ n ∈ A, (1 : ℝ) / (n : ℝ)}

/--
**Erdős Problem 856** — Upper bound [Er70]:

For every $k \geq 3$, there exists $C > 0$ such that for all sufficiently large $N$,
$$f_k(N) \leq C \cdot \frac{\log N}{\log(\log N)}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_856 (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      fk k N ≤ C * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) := by
  sorry

/--
**Erdős Problem 856** — Tang–Zhang lower bound [TaZh25b]:

For every $k \geq 3$, there exist constants $b$ with $0 < b \leq 1$ and $C > 0$ such that
for all sufficiently large $N$,
$$f_k(N) \geq C \cdot (\log N)^{b}.$$
-/
@[category research solved, AMS 5 11]
theorem erdos_856.variants.tang_zhang_lower (k : ℕ) (hk : k ≥ 3) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      fk k N ≥ C * (Real.log (N : ℝ)) ^ b := by
  sorry

/--
**Erdős Problem 856** — Tang–Zhang upper bound [TaZh25b]:

For every $k \geq 3$, there exist constants $c$ with $0 < c \leq 1$ and $C > 0$ such that
for all sufficiently large $N$,
$$f_k(N) \leq C \cdot (\log N)^{c}.$$

The exponents $c_k$ are $< 1$ (improving over the trivial bound) if and only if
the sunflower conjecture [857] holds for $k$-sunflowers.
-/
@[category research solved, AMS 5 11]
theorem erdos_856.variants.tang_zhang_upper (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      fk k N ≤ C * (Real.log (N : ℝ)) ^ c := by
  sorry

end Erdos856
