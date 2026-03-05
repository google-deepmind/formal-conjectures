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
# Erdős Problem 896

*Reference:* [erdosproblems.com/896](https://www.erdosproblems.com/896)

[Er72] Erdős, P., _Quelques problèmes de théorie des nombres_, p. 81, 1972.

Estimate the maximum of $F(A,B)$ as $A, B$ range over all subsets of $\{1,\ldots,N\}$,
where $F(A,B)$ counts the number of $m$ such that $m = ab$ has exactly one solution with
$a \in A$ and $b \in B$.

Van Doorn proved:
$$
(1 + o(1)) \frac{N^2}{\log N} \leq \max_{A,B} F(A,B) \ll \frac{N^2}{(\log N)^\delta (\log \log N)^{3/2}}
$$
where $\delta = 1 - \frac{1 + \log \log 2}{\log 2} \approx 0.086$.

The open problem is to determine the exact asymptotic order.
-/

open Finset Real

namespace Erdos896

/--
$F(A,B)$ counts the number of distinct products $m = a \cdot b$ (with $a \in A$, $b \in B$)
that have exactly one representation as such a product.
-/
def uniqueProductCount (A B : Finset ℕ) : ℕ :=
  ((A ×ˢ B).image (fun p => p.1 * p.2)).filter (fun m =>
    ((A ×ˢ B).filter (fun p => p.1 * p.2 = m)).card = 1) |>.card

/-- The maximum of $F(A,B)$ over all $A, B \subseteq \{1,\ldots,N\}$ is $O(N^2 / \log N)$,
i.e., the lower bound gives the correct order of magnitude. [Er72] -/
@[category research open, AMS 5 11]
theorem erdos_896 :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        (uniqueProductCount A B : ℝ) ≤ C * (N : ℝ) ^ 2 / Real.log (N : ℝ) := by
  sorry

/-- Known lower bound (van Doorn): for any $\varepsilon > 0$ and all sufficiently large $N$,
there exist $A, B \subseteq \{1,\ldots,N\}$ with
$F(A,B) \geq (1-\varepsilon) \cdot N^2 / \log N$. [Er72] -/
@[category research solved, AMS 5 11]
theorem erdos_896.variants.lower_bound :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
        (uniqueProductCount A B : ℝ) ≥ (1 - ε) * (N : ℝ) ^ 2 / Real.log (N : ℝ) := by
  sorry

end Erdos896
