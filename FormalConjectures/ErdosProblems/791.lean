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
# Erdős Problem 791

*Reference:* [erdosproblems.com/791](https://www.erdosproblems.com/791)

Let $g(n)$ be the minimal size of a set $A \subseteq \{0, \ldots, n\}$ such that
$\{0, \ldots, n\} \subseteq A + A$ (i.e., $A$ is a finite additive 2-basis for
$\{0, \ldots, n\}$). Estimate $g(n)$. In particular, is it true that
$g(n) \sim 2\sqrt{n}$?

A problem of Erdős [Er73], building on work of Rohrbach [Ro37].

Rohrbach [Ro37] proved $(2 + c) \cdot n \le g(n)^2 \le 4 \cdot n$ for some small $c > 0$.

The current best-known bounds are:
$$
(2.181\ldots + o(1)) \cdot n \le g(n)^2 \le (3.458\ldots + o(1)) \cdot n.
$$

The lower bound is due to Yu [Yu15], the upper bound to Kohonen [Ko17].
The disproof of $g(n) \sim 2\sqrt{n}$ was accomplished by Mrose [Mr79], who showed
$g(n)^2 \le \tfrac{7}{2} \cdot n$.
-/

open scoped Pointwise

namespace Erdos791

/-- `additiveBasesMinSize n` is the minimum cardinality of a set $A \subseteq \{0, \ldots, n\}$
such that every element of $\{0, \ldots, n\}$ can be written as a sum of two elements
of $A$ (a finite additive 2-basis). This is the function $g(n)$ in Erdős Problem 791. -/
noncomputable def additiveBasesMinSize (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧
    A ⊆ Finset.range (n + 1) ∧ Finset.range (n + 1) ⊆ A + A}

/--
Erdős Problem 791 — Best known lower bound (Yu [Yu15]):

For all $\varepsilon > 0$, for sufficiently large $n$,
$$
g(n)^2 \ge \left(\frac{2181}{1000} - \varepsilon\right) \cdot n.
$$

The constant $2181/1000$ approximates $2.181\ldots$
-/
@[category research solved, AMS 5 11]
theorem erdos_791.variants.lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ((2181 : ℝ) / 1000 - ε) * (n : ℝ) ≤ ((additiveBasesMinSize n : ℝ)) ^ 2 := by
  sorry

/--
Erdős Problem 791 — Best known upper bound (Kohonen [Ko17]):

For all $\varepsilon > 0$, for sufficiently large $n$,
$$
g(n)^2 \le \left(\frac{3459}{1000} + \varepsilon\right) \cdot n.
$$

The constant $3459/1000$ approximates $3.458\ldots$
-/
@[category research solved, AMS 5 11]
theorem erdos_791.variants.upper_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ((additiveBasesMinSize n : ℝ)) ^ 2 ≤ ((3459 : ℝ) / 1000 + ε) * (n : ℝ) := by
  sorry

/--
Erdős Problem 791 — Main open question [Er73]:

Determine the value of $\lim_{n \to \infty} g(n)^2 / n$, if it exists.
Currently known to lie in the interval $[2.181\ldots, 3.458\ldots]$.

Formalized as: there exists $c > 0$ such that $g(n)^2 = (c + o(1)) \cdot n$.
-/
@[category research open, AMS 5 11]
theorem erdos_791 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |((additiveBasesMinSize n : ℝ)) ^ 2 - c * (n : ℝ)| ≤ ε * (n : ℝ) := by
  sorry

end Erdos791
