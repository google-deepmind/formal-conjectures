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
# Erdős Problem 430

*Reference:* [erdosproblems.com/430](https://www.erdosproblems.com/430)

Fix an integer $n$ and define a decreasing sequence by $a_1 = n-1$ and, for $k \geq 2$,
$a_k$ is the greatest integer $m$ in $[2, a_{k-1})$ such that all prime factors of $m$
are $> n - m$. The sequence terminates when no such $m$ exists.

Conjecture: for sufficiently large $n$, not all terms of the sequence are prime.

Erdős and Graham [ErGr80] write 'preliminary calculations made by Selfridge indicate
that this is the case but no proof is in sight'. For example if $n = 8$ we have
$a_1 = 7$ and $a_2 = 5$ and then the sequence terminates.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Finset

namespace Erdos430

/-- The next term in the Erdős 430 sequence: the greatest $m$ in $[2, \text{prev})$ such that
all prime factors of $m$ are $> n - m$. The condition "all prime factors $> n - m$"
is equivalent to `Nat.minFac m > n - m`, i.e., $n < m + \operatorname{minFac}(m)$.
Returns $0$ if no such $m$ exists (sequence terminates). -/
def nextTerm (n prev : ℕ) : ℕ :=
  let S := (Ico 2 prev).filter (fun m => n < m + m.minFac)
  if h : S.Nonempty then S.max' h else 0

/-- The Erdős 430 sequence for a given $n$: $a(0) = n - 1$,
$a(k+1) = \operatorname{nextTerm}(n, a(k))$. Terms become $0$ once the sequence terminates. -/
def seq (n : ℕ) : ℕ → ℕ
  | 0 => n - 1
  | k + 1 => nextTerm n (seq n k)

/--
Erdős Problem 430 [ErGr80]:

For sufficiently large $n$, the greedy decreasing sequence in $[2, n)$ starting at
$n - 1$, where each term has all prime factors larger than its complement to $n$,
must contain a composite number.
-/
@[category research open, AMS 11]
theorem erdos_430 :
    answer(sorry) ↔
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, 2 ≤ seq n k ∧ ¬(seq n k).Prime) := by
  sorry

end Erdos430
