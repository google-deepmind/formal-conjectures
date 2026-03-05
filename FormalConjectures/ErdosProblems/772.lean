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
# Erdős Problem 772

*Reference:* [erdosproblems.com/772](https://www.erdosproblems.com/772)

Let $k \geq 1$ and $H_k(n)$ be the maximal $r$ such that if $A \subset \mathbb{N}$ has
$|A| = n$ and $\|1_A \ast 1_A\|_\infty \leq k$ (the additive representation function is
bounded by $k$) then $A$ contains a Sidon set of size at least $r$.

Is it true that $H_k(n)/n^{1/2} \to \infty$? Or even $H_k(n) > n^{1/2+c}$ for some
constant $c > 0$?

**Proved**: The answer is yes, and in fact $H_k(n) \gg_k n^{2/3}$, proved by
Alon and Erdős.

[AlEr85] Alon, N. and Erdős, P., *An application of graph theory to additive number theory*,
European J. Combin. 6 (1985), 201–203.
-/

namespace Erdos772

/-- A finite set of natural numbers is a Sidon set ($B_2$ set) if all pairwise
sums are distinct: for $a, b, c, d \in S$ with $a + b = c + d$, we have
$\{a, b\} = \{c, d\}$ as multisets. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The additive representation count: the number of ordered pairs $(a, b) \in A \times A$
with $a + b = m$. The condition $\|1_A \ast 1_A\|_\infty \leq k$ is equivalent to
$\operatorname{addRepCount}(A, m) \leq k$ for all $m$. -/
def addRepCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => a ≤ m ∧ (m - a) ∈ A)).card

/--
Erdős Problem 772 (Proved, Alon–Erdős [AlEr85]):

Is it true that $H_k(n)/n^{1/2} \to \infty$? The answer is yes: for every $k \geq 1$ and
every $C > 0$, eventually every $n$-element set with additive representation bounded by $k$
contains a Sidon subset of size at least $C \cdot n^{1/2}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_772 : answer(True) ↔
    ∀ k : ℕ, k ≥ 1 →
    ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset ℕ, A.card = n →
        (∀ m : ℕ, addRepCount A m ≤ k) →
        ∃ S : Finset ℕ, S ⊆ A ∧ IsSidonSet S ∧
          (S.card : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

/--
Erdős Problem 772 — stronger variant (Proved, Alon–Erdős [AlEr85]):

In fact $H_k(n) \gg_k n^{2/3}$: for each $k \geq 1$ there exist $C > 0$ and $N_0$ such that
for all $n \geq N_0$, every $n$-element set with additive representation bounded by $k$
contains a Sidon subset of size at least $C \cdot n^{2/3}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_772.variants.alon_erdos_bound :
    ∀ k : ℕ, k ≥ 1 →
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset ℕ, A.card = n →
        (∀ m : ℕ, addRepCount A m ≤ k) →
        ∃ S : Finset ℕ, S ⊆ A ∧ IsSidonSet S ∧
          (S.card : ℝ) ≥ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  sorry

end Erdos772
