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
# Erdős Problem 539

*Reference:* [erdosproblems.com/539](https://www.erdosproblems.com/539)

Let $h(n)$ be such that, for any set $A \subseteq \mathbb{N}$ of size $n$, the set
$$\left\{ \frac{a}{\gcd(a,b)} : a, b \in A \right\}$$
has size at least $h(n)$. Erdős and Szemerédi proved that $n^{1/2} \ll h(n) \ll n^{1-c}$ for some
constant $c > 0$. The upper bound has been improved to $h(n) \ll n^{2/3}$ by Freiman and Lev.
-/

open Finset

namespace Erdos539

/-- The set of gcd-quotients $\{a / \gcd(a, b) : a, b \in A\}$ for a finite set $A$ of
natural numbers. -/
def gcdQuotientSet (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 / Nat.gcd p.1 p.2)

/--
**Erdős Problem 539** (Lower bound, Erdős-Szemerédi):

There exists a constant $C > 0$ such that for any finite set $A$ of positive integers
of size $n$, the set $\{a / \gcd(a, b) : a, b \in A\}$ has size at least $C \cdot n^{1/2}$.
-/
@[category research solved, AMS 11]
theorem erdos_539 :
    ∃ C : ℝ, 0 < C ∧
    ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) →
      C * ((A.card : ℝ) ^ ((1 : ℝ) / 2)) ≤ ((gcdQuotientSet A).card : ℝ) := by
  sorry

/--
**Erdős Problem 539** (Upper bound, Freiman-Lev):

There exists a constant $C > 0$ such that for all sufficiently large $n$, there exists
a finite set $A$ of positive integers of size $n$ whose gcd-quotient set has size at most
$C \cdot n^{2/3}$.
-/
@[category research solved, AMS 11]
theorem erdos_539.variants.upper_bound :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ A.card = n ∧
        ((gcdQuotientSet A).card : ℝ) ≤ C * ((n : ℝ) ^ ((2 : ℝ) / 3)) := by
  sorry

end Erdos539
