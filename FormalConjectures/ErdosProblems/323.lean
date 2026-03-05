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
# Erdős Problem 323

If $f_{k,m}(x)$ counts the natural numbers at most $x$ that can be represented as a sum of $m$
nonnegative $k$-th powers, Erdős and Graham conjectured lower bounds on $f_{k,m}(x)$: that
$f_{k,k}(x) \gg_\varepsilon x^{1-\varepsilon}$ for every $\varepsilon > 0$, and that
$f_{k,m}(x) \gg x^{m/k}$ when $m < k$.

*Reference:* [erdosproblems.com/323](https://www.erdosproblems.com/323)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset Classical

open scoped BigOperators

namespace Erdos323

/-- An integer $n$ is a sum of $m$ nonnegative $k$-th powers if there exist
nonnegative integers $a_1, \ldots, a_m$ with $n = a_1^k + \cdots + a_m^k$. -/
def IsSumOfKthPowers (k m n : ℕ) : Prop :=
  ∃ a : Fin m → ℕ, n = ∑ i, (a i) ^ k

/-- $f_{k,m}(x)$ counts the number of natural numbers $\leq x$ which can be
represented as a sum of $m$ nonnegative $k$-th powers. -/
noncomputable def fKm (k m x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => IsSumOfKthPowers k m n)).card

/--
**Erdős Problem 323, Part 1** [ErGr80]:

For every $k \geq 1$ and $\varepsilon > 0$, $f_{k,k}(x) \gg_\varepsilon x^{1-\varepsilon}$,
i.e., there exists a constant $C > 0$ (depending on $k$ and $\varepsilon$) such that
$f_{k,k}(x) \geq C \cdot x^{1-\varepsilon}$ for all sufficiently large $x$.
-/
@[category research open, AMS 11]
theorem erdos_323 :
    ∀ k : ℕ, 1 ≤ k →
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      C * (x : ℝ) ^ (1 - ε) ≤ (fKm k k x : ℝ) := by
  sorry

/--
**Erdős Problem 323, Part 2** [ErGr80]:

For $1 \leq m < k$, $f_{k,m}(x) \gg x^{m/k}$, i.e., there exists a constant $C > 0$
(depending on $k$ and $m$) such that $f_{k,m}(x) \geq C \cdot x^{m/k}$ for all
sufficiently large $x$.
-/
@[category research open, AMS 11]
theorem erdos_323.variants.m_lt_k :
    ∀ k : ℕ, 2 ≤ k →
    ∀ m : ℕ, 1 ≤ m → m < k →
    ∃ C : ℝ, 0 < C ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      C * (x : ℝ) ^ ((m : ℝ) / (k : ℝ)) ≤ (fKm k m x : ℝ) := by
  sorry

end Erdos323
