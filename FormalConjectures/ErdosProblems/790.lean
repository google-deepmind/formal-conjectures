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
# Erdős Problem 790

*Reference:* [erdosproblems.com/790](https://www.erdosproblems.com/790)

Let $l(n)$ be maximal such that if $A \subset \mathbb{Z}$ with $|A| = n$ then there exists a
sum-free $B \subseteq A$ with $|B| \geq l(n)$ — that is, $B$ is such that there are no
solutions to $a_1 = a_2 + \cdots + a_r$ with $a_i \in B$ all distinct.

Choi, Komlós, and Szemerédi [CKS75] proved
$$
(n \log n / \log \log n)^{1/2} \ll l(n) \ll n / \log n.
$$
They further conjecture that $l(n) \geq n^{1 - o(1)}$.

[CKS75] Choi, S. L. G., Komlós, J., and Szemerédi, E., _On sum-free subsequences_,
Trans. Amer. Math. Soc. 212 (1975), 307–313.
-/

namespace Erdos790

/-- A finset $B \subseteq \mathbb{Z}$ is "sum-free" in the sense of Erdős Problem 790 if no
element of $B$ equals the sum of two or more other distinct elements of $B$. -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∀ S : Finset ℤ, S ⊆ B.erase b → S.card ≥ 2 → b ≠ S.sum id

/-- $l(n)$: the largest $l$ such that every $n$-element subset $A$ of $\mathbb{Z}$ contains a
sum-free subset $B$ with $|B| \geq l$. -/
noncomputable def maxSumFreeSize (n : ℕ) : ℕ :=
  sSup {l : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ l ≤ B.card ∧ IsSumFree B}

/--
**Erdős Problem 790** — Is it true that $l(n) n^{-1/2} \to \infty$? That is, for every $C > 0$
there exists $N_0$ such that $l(n) \geq C \cdot n^{1/2}$ for all $n \geq N_0$.
-/
@[category research open, AMS 5 11]
theorem erdos_790 : answer(sorry) ↔
    ∀ C : ℝ, C > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
**Erdős Problem 790** — Is it true that $l(n) < n^{1-c}$ for some $c > 0$? That is, there
exist $c > 0$ and $N_0$ such that $l(n) \leq n^{1-c}$ for all $n \geq N_0$.
-/
@[category research open, AMS 5 11]
theorem erdos_790.variants.upper_bound_conjecture : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≤ (n : ℝ) ^ (1 - c) := by
  sorry

/--
**Erdős Problem 790** — CKS lower bound [CKS75]:
$$
l(n) \gg \left(\frac{n \log n}{\log \log n}\right)^{1/2}.
$$
-/
@[category research solved, AMS 5 11]
theorem erdos_790.variants.cks_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≥
        C * ((n : ℝ) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2) := by
  sorry

/--
**Erdős Problem 790** — CKS upper bound [CKS75]:
$$
l(n) \ll \frac{n}{\log n}.
$$
-/
@[category research solved, AMS 5 11]
theorem erdos_790.variants.cks_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≤ C * ((n : ℝ) / Real.log (n : ℝ)) := by
  sorry

/--
**Erdős Problem 790** — CKS conjecture [CKS75]: $l(n) \geq n^{1 - o(1)}$, i.e., for every
$\varepsilon > 0$, there exists $N_0$ such that $l(n) \geq n^{1 - \varepsilon}$ for all
$n \geq N_0$.
-/
@[category research open, AMS 5 11]
theorem erdos_790.variants.cks_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≥ (n : ℝ) ^ (1 - ε) := by
  sorry

end Erdos790
