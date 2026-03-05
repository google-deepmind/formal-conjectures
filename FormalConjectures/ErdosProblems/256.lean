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
# Erdős Problem 256

*Reference:* [erdosproblems.com/256](https://www.erdosproblems.com/256)

Let $n \geq 1$ and $f(n)$ be maximal such that for any integers
$1 \leq a_1 \leq \cdots \leq a_n$,
$$\max_{|z|=1} \left|\prod_i (1 - z^{a_i})\right| \geq f(n).$$

Equivalently, $f(n)$ is the infimum over all non-decreasing sequences of positive
integers $(a_1, \ldots, a_n)$ of the supremum of $\left|\prod_i (1 - z^{a_i})\right|$ over the
unit circle.

Erdős conjectured that there exists $c > 0$ such that $\log f(n) \gg n^c$ [Er61, Er64b].

This specific conjecture was answered negatively by Belov and Konyagin [BeKo96],
who proved that $\log f(n) \ll (\log n)^4$. The broader problem of precisely
estimating $f(n)$ remains open.
-/

open Complex BigOperators Finset

namespace Erdos256

/-- The supremum of $\left|\prod_i (1 - z^{a_i})\right|$ as $z$ ranges over the unit circle,
for a fixed sequence of exponents $a$. -/
noncomputable def unitCircleMaxProd (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    y = ‖∏ i : Fin n, (1 - z ^ (a i))‖}

/-- $f(n)$ is the largest real number such that for any positive integers
$1 \leq a_1 \leq \cdots \leq a_n$, the maximum of $\left|\prod_i (1 - z^{a_i})\right|$
on the unit circle is at least $f(n)$. Equivalently, the infimum of
`unitCircleMaxProd` over all non-decreasing sequences of positive integers of
length $n$. -/
noncomputable def erdos256_f (n : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ (a : Fin n → ℕ),
    (∀ i, 0 < a i) ∧ Monotone a ∧
    y = unitCircleMaxProd n a}

/--
Erdős Conjecture (Problem 256) [Er61, Er64b]:

Does there exist a constant $c > 0$ such that $\log f(n) \gg n^c$, i.e., do there exist
constants $c > 0$ and $C > 0$ such that for all sufficiently large $n$,
$$\log f(n) \geq C \cdot n^c?$$

This was answered negatively by Belov and Konyagin [BeKo96], who showed
$\log f(n) \ll (\log n)^4$.
-/
@[category research solved, AMS 11 30]
theorem erdos_256 : answer(False) ↔
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.log (erdos256_f n) ≥ C * (n : ℝ) ^ c := by
  sorry

end Erdos256
