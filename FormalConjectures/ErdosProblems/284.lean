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
# Erdős Problem 284

*Reference:* [erdosproblems.com/284](https://www.erdosproblems.com/284)

Let $f(k)$ be the maximal value of $n_1$ such that there exist $n_1 < n_2 < \cdots < n_k$
with $1 = 1/n_1 + \cdots + 1/n_k$. Is it true that $f(k) = (1+o(1)) \, k/(e-1)$?

The upper bound $f(k) \leq (1+o(1)) \, k/(e-1)$ is trivial since for any $u \geq 1$ we have
$\sum_{u \leq n \leq eu} 1/n = 1 + o(1)$, and hence if $f(k) = u$ then $k \geq (e-1-o(1))u$.

Essentially solved by Croot [Cr01], who showed that for any $N > 1$ there exists
some $k \geq 1$ and $N < n_1 < \cdots < n_k \leq (e+o(1))N$ with $1 = \sum 1/n_i$.

[Cr01] Croot, E., _On a coloring conjecture about unit fractions_, Annals of Mathematics (2001).

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter Finset

namespace Erdos284

/-- $f(k)$ is the maximal value of the minimum element in any set of $k$ distinct positive
integers whose reciprocals sum to $1$. -/
noncomputable def erdos284_f (k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ (∀ n ∈ S, 0 < n) ∧
    S.sum (fun n => (1 : ℚ) / ↑n) = 1 ∧ m ∈ S ∧ ∀ n ∈ S, m ≤ n}

/--
Erdős Problem 284 (Proved) [ErGr80]:

$f(k) = (1+o(1)) \, k/(e-1)$, where $f(k)$ is the maximal minimum element in any
representation of $1$ as a sum of $k$ distinct unit fractions.

Equivalently, $f(k) \cdot (e-1) / k \to 1$ as $k \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_284 :
    answer(True) ↔
      Tendsto (fun k => (erdos284_f k : ℝ) * (Real.exp 1 - 1) / (k : ℝ))
        atTop (nhds 1) := by
  sorry

/--
The trivial upper bound $f(k) \leq (1+o(1)) \, k/(e-1)$, which follows from the fact that
$\sum_{u \leq n \leq eu} 1/n = 1 + o(1)$ for any $u \geq 1$.
-/
@[category research solved, AMS 11]
theorem erdos_284.variants.ub :
    Filter.limsup (fun k => (erdos284_f k : ℝ) * (Real.exp 1 - 1) / (k : ℝ))
      atTop ≤ 1 := by
  sorry

end Erdos284
