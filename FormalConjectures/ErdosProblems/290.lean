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
# Erdős Problem 290

*Reference:* [erdosproblems.com/290](https://www.erdosproblems.com/290)

Let $a \ge 1$. Must there exist some $b > a$ such that
$$\sum_{a \le n \le b} 1/n = r_1/s_1 \quad \text{and} \quad \sum_{a \le n \le b+1} 1/n = r_2/s_2,$$
with $(r_i, s_i) = 1$ and $s_2 < s_1$?

For example, $\sum_{3 \le n \le 5} 1/n = 47/60$ and $\sum_{3 \le n \le 6} 1/n = 19/20$,
and $20 < 60$.

This was resolved in the affirmative by van Doorn [vD24], who proved $b = b(a)$
always exists and $b(a) \ll a$. More precisely, $b(a) < 4.374a$ for all $a > 1$,
and $b(a) > a + 0.54 \log a$ for all large $a$.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).

[vD24] van Doorn, F., *On the denominators of harmonic numbers* (2024).
-/

open Finset

namespace Erdos290

/-- The partial harmonic sum $\sum_{n=a}^{b} 1/n$ as a rational number. -/
def harmonicPartialSum (a b : ℕ) : ℚ :=
  (Finset.Icc a b).sum (fun n => (1 : ℚ) / ↑n)

/--
Erdős Problem 290 (Proved) [ErGr80, p.34]:

For every $a \ge 1$, there exists $b > a$ such that the denominator of
$\sum_{n=a}^{b+1} 1/n$ (in lowest terms) is strictly less than the denominator
of $\sum_{n=a}^{b} 1/n$ (in lowest terms).
-/
@[category research solved, AMS 11]
theorem erdos_290 : answer(True) ↔
    ∀ a : ℕ, 1 ≤ a →
    ∃ b : ℕ, a < b ∧
      (harmonicPartialSum a (b + 1)).den < (harmonicPartialSum a b).den := by
  sorry

end Erdos290
