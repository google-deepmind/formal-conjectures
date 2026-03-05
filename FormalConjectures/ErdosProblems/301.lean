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
# Erdős Problem 301

Let $f(N)$ be the size of the largest subset of $\{1, \ldots, N\}$ such that no element has its
reciprocal equal to a sum of reciprocals of other elements. Erdős and Graham conjectured that
$f(N) = (1/2 + o(1))N$.

*Reference:* [erdosproblems.com/301](https://www.erdosproblems.com/301)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset BigOperators

namespace Erdos301

/-- A finset $A$ of positive integers is *unit-fraction-sum-free* if for no
element $a \in A$ can $1/a$ be expressed as a sum $\sum_{b \in S} 1/b$ for some
nonempty $S \subseteq A$ with $a \notin S$. That is, there are no solutions to
$1/a = 1/b_1 + \cdots + 1/b_k$ with distinct $a, b_1, \ldots, b_k \in A$. -/
def UnitFractionSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A → a ∉ S → S.Nonempty →
    ∑ b ∈ S, (1 : ℝ) / (b : ℝ) ≠ (1 : ℝ) / (a : ℝ)

/--
Erdős Problem 301 [ErGr80]:

Let $f(N)$ be the size of the largest $A \subseteq \{1, \ldots, N\}$ such that there are no
solutions to $1/a = 1/b_1 + \cdots + 1/b_k$ with distinct $a, b_1, \ldots, b_k \in A$.

Estimate $f(N)$. In particular, is it true that $f(N) = (1/2 + o(1))N$?

The example $A = (N/2, N] \cap \mathbb{N}$ shows that $f(N) \geq N/2$. Wouter van Doorn
has shown $f(N) \leq (25/28 + o(1))N$.

We formalize the conjectured statement: for every $\varepsilon > 0$, for all
sufficiently large $N$,
(1) every unit-fraction-sum-free $A \subseteq \{1, \ldots, N\}$ has
$|A| \leq (1/2 + \varepsilon)N$, and
(2) there exists a unit-fraction-sum-free $A \subseteq \{1, \ldots, N\}$ with
$|A| \geq (1/2 - \varepsilon)N$.
-/
@[category research open, AMS 5 11]
theorem erdos_301 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → UnitFractionSumFree A →
          (A.card : ℝ) ≤ (1 / 2 + ε) * (N : ℝ)) ∧
        (∃ (A : Finset ℕ), A ⊆ Finset.Icc 1 N ∧ UnitFractionSumFree A ∧
          (A.card : ℝ) ≥ (1 / 2 - ε) * (N : ℝ)) := by
  sorry

end Erdos301
