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
# Erdős Problem 176

*Reference:* [erdosproblems.com/176](https://www.erdosproblems.com/176)

Let $N(k, \ell)$ be the minimal $N$ such that for any $f : \{1,\ldots,N\} \to \{-1,1\}$,
there must exist a $k$-term arithmetic progression $P$ such that
$|\sum_{n \in P} f(n)| \geq \ell$.

Is it true that for any $c > 0$ there exists some $C > 1$ such that
$N(k, ck) \leq C^k$? What about $N(k, 2) \leq C^k$ or $N(k, \sqrt{k}) \leq C^k$?

When $\ell = k$, $N(k, k)$ is the van der Waerden number $W(k)$.

[Er65b] Erdős, P., _Extremal problems in number theory_ (1965).

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo.,
1971) (1973), 117-138.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators Real

namespace Erdos176

/-- The arithmetic progression discrepancy number $N(k, \ell)$: the minimal $N$ such
that for every $f : \{1,\ldots,N\} \to \{-1,1\}$, there exists a $k$-term arithmetic
progression $a, a+d, \ldots, a+(k-1)d$ with $d \geq 1$ and all terms in $\{1,\ldots,N\}$
such that $|\sum_i f(a + id)| \geq \ell$. -/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ :=
  sInf { N : ℕ | ∀ f : ℕ → ℤ,
    (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
    ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
      ℓ ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| }

/--
Erdős Conjecture (Problem 176) [Er65b, Er73, ErGr80]:
For any $c > 0$, there exists some $C > 1$ such that $N(k, ck) \leq C^k$.
-/
@[category research open, AMS 5 11]
theorem erdos_176 :
    answer(sorry) ↔
    ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (c * ↑k) : ℝ) ≤ C ^ k := by
  sorry

/--
Erdős Conjecture (Problem 176, variant) [Er65b, Er73, ErGr80]:
There exists some $C > 1$ such that $N(k, 2) \leq C^k$.
-/
@[category research open, AMS 5 11]
theorem erdos_176.variants.constant_discrepancy :
    answer(sorry) ↔
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k 2 : ℝ) ≤ C ^ k := by
  sorry

/--
Erdős Conjecture (Problem 176, variant) [Er65b, Er73, ErGr80]:
There exists some $C > 1$ such that $N(k, \sqrt{k}) \leq C^k$.
-/
@[category research open, AMS 5 11]
theorem erdos_176.variants.sqrt_discrepancy :
    answer(sorry) ↔
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (Real.sqrt ↑k) : ℝ) ≤ C ^ k := by
  sorry

end Erdos176
