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
# Erdős Problem 709

*Reference:* [erdosproblems.com/709](https://www.erdosproblems.com/709)

Let $f(n)$ be minimal such that, for any $A = \{a_1, \ldots, a_n\} \subseteq [2, \infty) \cap \mathbb{N}$
of size $n$, in any interval $I$ of $f(n) \cdot \max(A)$ consecutive integers there exist distinct
$x_1, \ldots, x_n \in I$ such that $a_i \mid x_i$.

Obtain good bounds for $f(n)$, or even an asymptotic formula.

A problem of Erdős and Surányi [ErSu59], who proved
$(\log n)^c \ll f(n) \ll n^{1/2}$
for some constant $c > 0$.

See also [708].

[ErSu59] Erdős, P. and Surányi, J. (1959).
-/

open Nat Finset

namespace Erdos709

/-- $f(n)$ for Erdős Problem 709: the minimal $f$ such that for any $A \subseteq \{2, 3, \ldots\}$
with $|A| = n$ and any interval of $f \cdot \max(A)$ consecutive integers starting at $k$,
there exist distinct $x_1, \ldots, x_n$ in the interval with $a_i \mid x_i$.

Formally, the infimum of all $f$ such that for every such $A$ there exists an
injective assignment $g : A \to \text{interval}$ with $a \mid g(a)$ for all $a \in A$. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℕ) (hA : A.Nonempty),
    A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ k : ℕ,
    ∃ g : ℕ → ℕ,
      (∀ a ∈ A, g a ∈ Finset.Icc k (k + m * A.max' hA - 1)) ∧
      (∀ a ∈ A, a ∣ g a) ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → g a₁ ≠ g a₂)}

/--
Erdős Problem 709, known lower bound [ErSu59]:

There exist constants $c > 0$ and $C > 0$ such that for all sufficiently large $n$,
$f(n) \geq C \cdot (\log n)^c$.
-/
@[category research solved, AMS 5 11]
theorem erdos_709 :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (f n : ℝ) ≥ C * (Real.log n) ^ c := by
  sorry

/--
Erdős Problem 709, known upper bound [ErSu59]:

There exist $C > 0$ and $N_0$ such that for all $n \geq N_0$,
$f(n) \leq C \cdot n^{1/2}$.
-/
@[category research solved, AMS 5 11]
theorem erdos_709.variants.upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (f n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  sorry

end Erdos709
