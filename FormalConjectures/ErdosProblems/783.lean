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
# Erdős Problem 783

*Reference:* [erdosproblems.com/783](https://www.erdosproblems.com/783)

Fix some constant $C > 0$ and let $N$ be large. Let $A \subseteq \{2, \ldots, N\}$ be such that
$(a, b) = 1$ for all $a \neq b \in A$ and $\sum_{n \in A} 1/n \leq C$.

What choice of such an $A$ minimises the number of integers $m \leq N$ not divisible
by any $a \in A$?

Erdős suggests the optimal set is consecutive largest primes up to $N$.
Tao conjectures the minimum is $(\rho(e^C) + o(1))N$ where $\rho$ is the Dickman function.
-/

open Finset BigOperators

namespace Erdos783

/-- The Dickman rho function, the unique continuous function $\rho : \mathbb{R} \to \mathbb{R}$
satisfying $\rho(u) = 1$ for $0 \leq u \leq 1$ and $u \cdot \rho'(u) = -\rho(u-1)$ for
$u > 1$. -/
noncomputable opaque dickmanRho : ℝ → ℝ

/-- Count of integers in $\{1, \ldots, N\}$ not divisible by any element of $A$. -/
def unsievedCount (N : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range N).image (· + 1)).filter
    (fun m => ∀ a ∈ A, ¬(a ∣ m)) |>.card

/--
Erdős Problem 783 (Tao's formulation):

For any $C > 0$, the minimum number of integers in $\{1, \ldots, N\}$ not divisible by
any element of a pairwise coprime set $A \subseteq \{2, \ldots, N\}$ with
$\sum_{a \in A} 1/a \leq C$ is asymptotically $\rho(e^C) \cdot N$, where $\rho$ is the
Dickman function.

That is, for every $\varepsilon > 0$ and large enough $N$:
(1) There exists a valid $A$ with unsieved count $\leq (\rho(e^C) + \varepsilon) \cdot N$.
(2) Every valid $A$ has unsieved count $\geq (\rho(e^C) - \varepsilon) \cdot N$.
-/
@[category research open, AMS 11]
theorem erdos_783 (C : ℝ) (hC : C > 0) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∃ (A : Finset ℕ),
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ N) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) ∧
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ) ≤ C) ∧
        (unsievedCount N A : ℝ) ≤ (dickmanRho (Real.exp C) + ε) * ↑N) ∧
      (∀ (A : Finset ℕ),
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ N) →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) →
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ) ≤ C) →
        (dickmanRho (Real.exp C) - ε) * ↑N ≤ (unsievedCount N A : ℝ)) := by
  sorry

end Erdos783
