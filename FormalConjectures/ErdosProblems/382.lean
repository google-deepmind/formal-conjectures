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
# Erdős Problem 382

Let $u \le v$ be such that the largest prime dividing $\prod_{u \le m \le v} m$ appears with
exponent at least $2$. The problem asks whether $v - u = v^{o(1)}$ and whether $v - u$ can be
arbitrarily large.

*Reference:* [erdosproblems.com/382](https://www.erdosproblems.com/382)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Real

namespace Erdos382

/-- The largest prime factor of a natural number $n$. Returns $0$ if $n \le 1$. -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- An interval $[u, v]$ has its largest prime factor appearing with exponent $\ge 2$
in the factorization of the product $\prod_{u \le m \le v} m$. -/
noncomputable def HasSquaredLargestPrime (u v : ℕ) : Prop :=
  let P := ∏ m ∈ Finset.Icc u v, m
  let p := largestPrimeFactor P
  u ≤ v ∧ 0 < p ∧ 1 < P.factorization p

/--
Erdős Problem 382 (Part 1) [ErGr80]:

Let $u \le v$ be such that the largest prime dividing $\prod_{u \le m \le v} m$ appears with
exponent at least $2$. Is it true that $v - u = v^{o(1)}$?

This means: for every $\varepsilon > 0$, for all sufficiently large $v$, if the interval $[u,v]$
has its largest prime factor appearing with exponent $\ge 2$, then $v - u \le v^{\varepsilon}$.
-/
@[category research open, AMS 11]
theorem erdos_382 :
    answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ u v : ℕ, N₀ ≤ v →
      HasSquaredLargestPrime u v →
      ((v : ℝ) - (u : ℝ)) ≤ (v : ℝ) ^ ε := by
  sorry

/--
Erdős Problem 382 (Part 2) [ErGr80]:

Can $v - u$ be arbitrarily large? That is, for every $k$, do there exist $u \le v$
with $v - u \ge k$ such that the largest prime dividing $\prod_{u \le m \le v} m$ appears
with exponent at least $2$?
-/
@[category research open, AMS 11]
theorem erdos_382.variants.arbitrarily_large :
    answer(sorry) ↔
    ∀ k : ℕ, ∃ u v : ℕ, k ≤ v - u ∧ HasSquaredLargestPrime u v := by
  sorry

end Erdos382
