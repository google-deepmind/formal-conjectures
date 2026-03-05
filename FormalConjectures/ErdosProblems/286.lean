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
# Erdős Problem 286

*Reference:* [erdosproblems.com/286](https://www.erdosproblems.com/286)

For sufficiently large $k$, do there exist $k$ distinct positive integers in an interval of
width $(e - 1 + o(1))k$ whose reciprocals sum to $1$? Solved affirmatively by Croot.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathématique (1980).

[Cr01] Croot, E., *On a coloring conjecture about unit fractions*. Annals of Mathematics (2001).
-/

open Filter Finset

namespace Erdos286

/--
[ErGr80, p.33] (Proved by Croot [Cr01]):
Let $k \geq 2$. Is it true that there exists an interval $I$ of width $(e - 1 + o(1))k$
and integers $n_1 < \cdots < n_k \in I$ such that
$$1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}?$$

The answer is yes. For every $\varepsilon > 0$, for all sufficiently large $k$, there
exist $k$ distinct positive integers in an interval of width at most
$(e - 1 + \varepsilon)k$ whose reciprocals sum to $1$.
-/
@[category research solved, AMS 11]
theorem erdos_286 :
    answer(True) ↔
    ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∃ S : Finset ℕ,
      S.card = k ∧
      (∀ n ∈ S, 0 < n) ∧
      (∃ a : ℕ, ∀ n ∈ S, a ≤ n ∧ (n : ℝ) ≤ (a : ℝ) + (Real.exp 1 - 1 + ε) * (k : ℝ)) ∧
      S.sum (fun n => (1 : ℚ) / ↑n) = 1 := by
  sorry

end Erdos286
