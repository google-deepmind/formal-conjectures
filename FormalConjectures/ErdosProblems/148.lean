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
# Erdős Problem 148

*Reference:* [erdosproblems.com/148](https://www.erdosproblems.com/148)

Let $F(k)$ be the number of solutions to $1 = 1/n_1 + \cdots + 1/n_k$ where
$1 \le n_1 < n_2 < \cdots < n_k$ are distinct positive integers.
Find good estimates for $F(k)$.

The current best known bounds are
$$2^{c^{k/\log k}} \le F(k) \le c_0^{(1/5 + o(1)) \cdot 2^k}$$
where $c > 0$ is some absolute constant and $c_0 = 1.26408\cdots$ is the Vardi constant.
The lower bound is due to Konyagin [Ko14] and the upper bound to
Elsholtz and Planitzer [ElPl21].

[Ko14] Konyagin, S., _On the number of representations of an integer as a sum of distinct
unit fractions_, 2014.

[ElPl21] Elsholtz, C. and Planitzer, S., _The number of solutions of the Erdős–Straus
equation and sums of $k$ unit fractions_, Proc. R. Soc. Edinb. A Math. (2021).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_, Monographies de L'Enseignement Mathématique (1980).
-/

open BigOperators Real Filter

namespace Erdos148

/-- $F(k)$ is the number of $k$-element sets of positive integers
whose unit fractions sum to $1$: $1/n_1 + \cdots + 1/n_k = 1$. -/
noncomputable def egyptianFractionCount (k : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | S.card = k ∧ (∀ n ∈ S, 0 < n) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1}

/-- Konyagin lower bound [Ko14]:
There exists an absolute constant $c > 0$ such that
$2^{c^{k/\log k}} \le F(k)$ for all sufficiently large $k$. -/
@[category research solved, AMS 11]
theorem erdos_148.variants.konyagin_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (c ^ ((k : ℝ) / Real.log k)) ≤
        (egyptianFractionCount k : ℝ) := by
  sorry

/-- Elsholtz–Planitzer upper bound [ElPl21]:
There exists a constant $c_0 > 1$ (the Vardi constant, $c_0 \approx 1.26408$) such that
for every $\varepsilon > 0$, $F(k) \le c_0^{(1/5 + \varepsilon) \cdot 2^k}$ for all
sufficiently large $k$. -/
@[category research solved, AMS 11]
theorem erdos_148.variants.elsholtz_planitzer_upper_bound :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (egyptianFractionCount k : ℝ) ≤
        c₀ ^ ((1 / 5 + ε) * (2 : ℝ) ^ (k : ℕ)) := by
  sorry

/-- Erdős Problem 148 [ErGr80, p. 32]:
Find good estimates for $F(k)$, the number of representations of $1$
as a sum of exactly $k$ distinct unit fractions.

The open problem is to close the gap between the known bounds. This
conjecture asserts that the correct order of magnitude is exponential
in $2^k$: there exist constants $1 < c_1 \le c_2$ such that
$c_1^{2^k} \le F(k) \le c_2^{2^k}$ for all sufficiently large $k$.
In particular, the Konyagin lower bound should be improvable to
exponential in $2^k$ to match the Elsholtz–Planitzer upper bound. -/
@[category research open, AMS 11]
theorem erdos_148 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ 1 < c₂ ∧ ∀ᶠ k : ℕ in atTop,
      c₁ ^ ((2 : ℝ) ^ (k : ℕ)) ≤ (egyptianFractionCount k : ℝ) ∧
      (egyptianFractionCount k : ℝ) ≤ c₂ ^ ((2 : ℝ) ^ (k : ℕ)) := by
  sorry

end Erdos148
