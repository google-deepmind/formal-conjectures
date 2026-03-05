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
# Erdős Problem 1025

*Reference:* [erdosproblems.com/1025](https://www.erdosproblems.com/1025)

Let $f$ be a function from all pairs of elements in $\{1,\ldots,n\}$ to $\{1,\ldots,n\}$ such
that $f(x,y) \neq x$ and $f(x,y) \neq y$ for all $x,y$. We call $X \subseteq \{1,\ldots,n\}$
independent if whenever $x,y \in X$ we have $f(x,y) \notin X$.

Let $g(n)$ be such that, in every function $f$, there is an independent set of
size at least $g(n)$. Estimate $g(n)$.

A question of Erdős and Hajnal [ErHa58], who proved
$n^{1/3} \ll g(n) \ll (n \log n)^{1/2}$.
Spencer [Sp72] proved $g(n) \gg n^{1/2}$.
Conlon, Fox, and Sudakov [CFS16] proved $g(n) \ll n^{1/2}$.
Thus $g(n) = \Theta(\sqrt{n})$.

[ErHa58] Erdős, P. and Hajnal, A., 1958.

[Sp72] Spencer, J., 1972.

[CFS16] Conlon, D., Fox, J., and Sudakov, B., 2016.
-/

open Finset

namespace Erdos1025

/-- A pair function on `Fin n` assigns to each pair of distinct elements
a third element different from both. -/
def IsValidPairFunction (n : ℕ) (f : Fin n → Fin n → Fin n) : Prop :=
  ∀ x y : Fin n, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/-- A set $S \subseteq \operatorname{Fin} n$ is independent with respect to $f$ if for all
distinct $x, y \in S$, we have $f(x,y) \notin S$. -/
def IsIndependentPairSet (n : ℕ) (f : Fin n → Fin n → Fin n)
    (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x y ∉ S

/--
Erdős Problem 1025, lower bound (Spencer [Sp72]):

For every valid pair function $f$ on $\operatorname{Fin} n$, there exists an independent set
of size at least $C \cdot \sqrt{n}$, for some absolute constant $C > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_1025 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, ∀ f : Fin n → Fin n → Fin n,
    IsValidPairFunction n f →
    ∃ S : Finset (Fin n), IsIndependentPairSet n f S ∧
      (S.card : ℝ) ≥ C * Real.sqrt n := by
  sorry

/--
Erdős Problem 1025, upper bound (Conlon–Fox–Sudakov [CFS16]):

There exists a constant $C > 0$ such that for all sufficiently large $n$,
there exists a valid pair function $f$ on $\operatorname{Fin} n$ for which every independent
set has size at most $C \cdot \sqrt{n}$.
-/
@[category research solved, AMS 5]
theorem erdos_1025.variants.upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∃ f : Fin n → Fin n → Fin n, IsValidPairFunction n f ∧
    ∀ S : Finset (Fin n), IsIndependentPairSet n f S →
      (S.card : ℝ) ≤ C * Real.sqrt n := by
  sorry

end Erdos1025
