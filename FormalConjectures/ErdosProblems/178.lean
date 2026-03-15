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
# Erdős Problem 178

*Reference:* [erdosproblems.com/178](https://www.erdosproblems.com/178)

Let $A_1, A_2, \ldots$ be an infinite collection of infinite sets of integers,
say $A_i = \{a_{i1} < a_{i2} < \cdots\}$. Does there exist some
$f : \mathbb{N} \to \{-1, 1\}$ such that
$$\max_{m,\; 1 \leq i \leq d} \left|\sum_{1 \leq j \leq m} f(a_{ij})\right| \ll_d 1$$
for all $d \geq 1$?

Erdős remarked "it seems certain that the answer is affirmative". This was proved by
Beck [Be81]. Beck [Be17] later proved that one can replace $\ll_d 1$ with
$\ll d^{4+\varepsilon}$ for any $\varepsilon > 0$.

[ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory. I*.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*. Monographies de L'Enseignement Mathématique (1980).

[Be81] Beck, J., *Balancing families of integer sequences*.
Combinatorica (1981), 209–216.

[Be17] Beck, J., *A discrepancy problem: balancing infinite dimensional vectors*. Number
theory—Diophantine problems, uniform distribution and applications (2017), 61–82.
-/

open Finset BigOperators

namespace Erdos178

/--
Erdős Problem 178 [ErGr79, ErGr80]:
Given any infinite sequence of infinite subsets of $\mathbb{N}$ (each represented by
its strictly increasing enumeration $a(i, \cdot) : \mathbb{N} \to \mathbb{N}$), there exists a
coloring $f : \mathbb{N} \to \mathbb{Z}$ with $f(n) \in \{-1, 1\}$ such that for each $d$, the partial
sums of $f$ along the first $d$ sequences are uniformly bounded by a constant
depending only on $d$.

Proved by Beck [Be81].
-/
@[category research solved, AMS 5]
theorem erdos_178 :
    answer(True) ↔
      ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
        ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
          ∀ d : ℕ, ∃ C : ℤ, 0 < C ∧
            ∀ m i, i < d → |∑ j ∈ Finset.range m, f (a i j)| ≤ C := by
  sorry

/--
Erdős Problem 178 — Beck's refinement [Be17]:
Beck proved the stronger result that the bound constant can be taken to grow
polynomially in $d$: for every $\varepsilon > 0$, the partial sums can be bounded
by $C \cdot d^{4+\varepsilon}$ for some absolute constant $C > 0$.
-/
@[category research solved, AMS 5]
theorem erdos_178_beck_refinement :
    answer(True) ↔
      ∀ ε : ℝ, 0 < ε →
        ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
          ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
            ∃ C : ℝ, 0 < C ∧
              ∀ d m i, i < d →
                (|∑ j ∈ Finset.range m, f (a i j)| : ℝ) ≤ C * (↑d) ^ ((4 : ℝ) + ε) := by
  sorry

end Erdos178
