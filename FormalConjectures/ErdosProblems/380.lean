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
# Erdős Problem 380

*Reference:* [erdosproblems.com/380](https://www.erdosproblems.com/380)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators

namespace Erdos380

/-- The largest prime factor of a natural number $n$. Returns $0$ if $n \le 1$. -/
noncomputable def largestPrimeFactor380 (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- An interval $[u, v]$ is *bad* if the greatest prime factor of $\prod_{u \le m \le v} m$
occurs with exponent greater than $1$ in the factorization of that product. -/
def IsBadInterval (u v : ℕ) : Prop :=
  let P := ∏ m ∈ Finset.Icc u v, m
  let p := largestPrimeFactor380 P
  u ≤ v ∧ 0 < p ∧ 1 < P.factorization p

/-- A natural number $n$ is contained in at least one bad interval. -/
def InBadInterval (n : ℕ) : Prop :=
  ∃ u v : ℕ, u ≤ n ∧ n ≤ v ∧ IsBadInterval u v

/-- $B(x)$: the number of $n \le x$ contained in at least one bad interval. -/
noncomputable def B380 (x : ℕ) : ℕ :=
  Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ x ∧ InBadInterval n}

/-- The count of $n \le x$ such that $P(n)^2 \mid n$, where $P(n)$ is the largest prime
factor. -/
noncomputable def squareDivCount380 (x : ℕ) : ℕ :=
  Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ x ∧
    0 < largestPrimeFactor380 n ∧ (largestPrimeFactor380 n) ^ 2 ∣ n}

/--
Erdős Problem 380 [ErGr80, p. 73]:

We call an interval $[u,v]$ *bad* if the greatest prime factor of $\prod_{u \le m \le v} m$
occurs with an exponent greater than $1$. Let $B(x)$ count the number of $n \le x$ which
are contained in at least one bad interval. Is it true that
$$B(x) \sim \#\{n \le x : P(n)^2 \mid n\},$$
where $P(n)$ is the largest prime factor of $n$?

The asymptotic equivalence $B(x) \sim f(x)$ is formalized as: for every $\varepsilon > 0$, for
sufficiently large $x$, $(1 - \varepsilon) \cdot f(x) \le B(x) \le (1 + \varepsilon) \cdot f(x)$.
-/
@[category research open, AMS 11]
theorem erdos_380 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (1 - ε) * (squareDivCount380 x : ℝ) ≤ (B380 x : ℝ) ∧
      (B380 x : ℝ) ≤ (1 + ε) * (squareDivCount380 x : ℝ) := by
  sorry

end Erdos380
