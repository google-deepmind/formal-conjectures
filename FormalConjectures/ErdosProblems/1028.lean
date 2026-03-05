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
# Erdős Problem 1028

*Reference:* [erdosproblems.com/1028](https://www.erdosproblems.com/1028)

Let $H(n) = \min_f \max_{X \subseteq \{1,\ldots,n\}} \left|\sum_{x \neq y \in X} f(x,y)\right|$,
where $f$ ranges over all functions $f\colon \{1,\ldots,n\}^2 \to \{-1,1\}$. Estimate $H(n)$.

Erdős [Er63d] proved $n/4 \le H(n) \ll n^{3/2}$.
Erdős and Spencer [ErSp71] proved that $H(n) \gg n^{3/2}$.

Together these give $H(n) = \Theta(n^{3/2})$.
-/

open Finset

namespace Erdos1028

/-- The discrepancy sum of a $\pm 1$ function $f$ over a subset $X$ of $\operatorname{Fin}(n)$:
$\sum_{x \neq y \in X} f(x, y)$ over ordered pairs with $x \neq y$. -/
def discrepancySum (n : ℕ) (f : Fin n → Fin n → ℤ) (X : Finset (Fin n)) : ℤ :=
  X.sum fun x => (X.filter (· ≠ x)).sum fun y => f x y

/--
Erdős Problem 1028 [Er63d][ErSp71]:

$H(n) = \Theta(n^{3/2})$, where
$H(n) = \min_f \max_{X \subseteq \{1,\ldots,n\}} \left|\sum_{x \neq y \in X} f(x,y)\right|$
and $f$ ranges over all $\pm 1$ valued functions on pairs.

This is equivalent to two bounds:
- Lower bound (Erdős–Spencer [ErSp71]): every $\pm 1$ function $f$ has some subset $X$
  with discrepancy at least $C_1 \cdot n^{3/2}$.
- Upper bound (Erdős [Er63d]): there exists a $\pm 1$ function $f$ such that all subsets
  have discrepancy at most $C_2 \cdot n^{3/2}$.
-/
@[category research solved, AMS 5]
theorem erdos_1028 :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    -- Lower bound: every ±1 function has a subset with large discrepancy
    (∀ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) →
      ∃ X : Finset (Fin n),
        C₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ |(discrepancySum n f X : ℝ)|) ∧
    -- Upper bound: there exists a ±1 function with all discrepancies bounded
    (∃ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) ∧
      ∀ X : Finset (Fin n),
        |(discrepancySum n f X : ℝ)| ≤ C₂ * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

end Erdos1028
