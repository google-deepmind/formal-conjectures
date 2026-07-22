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

import FormalConjecturesUtil

/-!
# Erdős Problem 178

*References:*
- [erdosproblems.com/178](https://www.erdosproblems.com/178)
- [ErGr79] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number theory: van der Waerden's theorem and related topics*. Enseign. Math. (1979), 325-344.
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number theory*. Monographies de L'Enseignement Mathématique (1980).
- [Be81] Beck, József, *Balancing families of integer sequences*. Combinatorica (1981), 209-216.
- [Be17] Beck, József, *A discrepancy problem: balancing infinite dimensional vectors*. Number theory—Diophantine problems, uniform distribution and applications (2017), 61-82.
-/

namespace Erdos178

open Finset BigOperators

/--
Let $A_1,A_2,\ldots$ be an infinite collection of infinite sets of integers, say
$A_i=\{a_{i1}<a_{i2}<\cdots\}$. Does there exist some $f:\mathbb{N}\to\{-1,1\}$ such that
\[\max_{m, 1\leq i\leq d} \left\lvert \sum_{1\leq j\leq m} f(a_{ij})\right\rvert \ll_d 1\]
for all $d\geq 1$?

Erdős remarks 'it seems certain that the answer is affirmative'. This was solved by Beck [Be81]. Recently Beck [Be17] proved that one can replace $\ll_d 1$ with $\ll d^{4+\epsilon}$ for any $\epsilon>0$.
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos178.lean"]
theorem erdos_178 : answer(True) ↔
    ∀ (a : ℕ → ℕ → ℕ) (ha : ∀ i, StrictMono (a i)),
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, ∃ C : ℕ, ∀ m i : ℕ, i < d →
        |∑ j ∈ range m, f (a i j)| ≤ ↑C := by
  sorry

end Erdos178
