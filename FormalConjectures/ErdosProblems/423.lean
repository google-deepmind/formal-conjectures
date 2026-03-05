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
# Erdős Problem 423

*Reference:* [erdosproblems.com/423](https://www.erdosproblems.com/423)

Let $a_1 = 1$ and $a_2 = 2$, and for $k \ge 3$ choose $a_k$ to be the least integer
$> a_{k-1}$ which is the sum of at least two consecutive terms of the sequence. What is
the asymptotic behaviour of this sequence?

The sequence begins $1, 2, 3, 5, 6, 8, 10, 11, \ldots$ (OEIS A005243).

Asked by Hofstadter (Erdős says Hofstadter was inspired by a similar question of Ulam).
Bolan and Tang have independently proved that $a_n - n$ is nondecreasing and unbounded,
so there are infinitely many integers not appearing in the sequence.

[Er77c] Erdős, P., *Problems and results on combinatorial number theory*, 1977.

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
number theory*, Monographies de L'Enseignement Mathématique (1980).
-/

open Finset BigOperators

namespace Erdos423

/-- `IsConsecutiveBlockSum a k m` means that $m$ equals the sum of at least two
    consecutive terms of the sequence $a$, using indices from $\{1, \ldots, k - 1\}$.
    That is, there exist $i, j$ with $1 \le i$, $i + 1 \le j$, $j \le k - 1$ such that
    $m = a(i) + a(i+1) + \cdots + a(j)$. -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$,
    $a(k)$ is the least integer $> a(k-1)$ that equals the sum of at least two
    consecutive terms from $\{a(1), \ldots, a(k-1)\}$. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/--
Erdős Problem 423 [Er77c, p.71; ErGr80, p.83]:

Let $a(1) = 1$, $a(2) = 2$, and for $k \ge 3$ let $a(k)$ be the least integer greater
than $a(k-1)$ that is a sum of at least two consecutive terms of the sequence.
Then $a(n) - n \to \infty$ as $n \to \infty$.

Equivalently, there are infinitely many positive integers not in the range of $a$.
This was proved independently by Bolan and Tang. The full asymptotic behaviour
of the sequence remains an open question.
-/
@[category research solved, AMS 5 11]
theorem erdos_423 :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M + n ≤ a n := by
  sorry

end Erdos423
