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
module

public import FormalConjecturesUtil

/-!
# Largest smallest-base in a decomposition of $n$ into at most four squares

The sequence $a(n)$ is the largest integer $k$ such that $n = k^2 + \dots$ is a
decomposition of $n$ into a sum of at most four nondecreasing squares:
$$a(n) = \max \{k \ge 1 : \exists b_1, b_2, b_3 \in \{0\} \cup [k, n],
  k^2 + b_1^2 + b_2^2 + b_3^2 = n\}$$

*References:*
- [A241898](https://oeis.org/A241898)
-/

@[expose] public section

namespace OeisA241898

open Finset

/-- Predicate testing whether $k$ is the smallest base in a decomposition of $n$ into a sum
of at most four squares. -/
def isValidBase (n k : ℕ) : Bool :=
  let S := 0 :: List.range' k (n - k + 1)
  0 < k && S.any fun b1 => S.any fun b2 => S.any fun b3 =>
    k ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 == n

/-- Largest integer $k$ such that $n = k^2 + \dots$ is a decomposition of $n$ into a sum
of at most four nondecreasing squares. -/
def a (n : ℕ) : ℕ :=
  ((Icc 1 n).filter (fun k => isValidBase n k)).max.getD 0

@[category test, AMS 11]
theorem a_1 : a 1 = 1 := by
  decide

@[category test, AMS 11]
theorem a_2 : a 2 = 1 := by
  decide

@[category test, AMS 11]
theorem a_3 : a 3 = 1 := by
  decide

@[category test, AMS 11]
theorem a_4 : a 4 = 2 := by
  decide

@[category test, AMS 11]
theorem a_5 : a 5 = 1 := by
  decide

/--
"From the data that I have, it would seem that $a(n)$ is greater than $7$ for all $n > 599$."
- _David S. Newman_, May 02 2014

This is false: since every four-square decomposition of a multiple of $8$ uses only even squares,
$a(4m) = 2a(m)$ for all even $m \ge 2$. From $a(46) = 1$ (via $46 = 1^2 + 3^2 + 6^2$) we obtain
$a(184) = 2$ and $a(736) = a(16 \cdot 46) = 4 \le 7$.
-/
@[category research solved, AMS 11]
theorem conjecture_1 : ¬ ∀ n : ℕ, 599 < n → 7 < a n := by
  sorry

/--
"By Lagrange's Theorem every number can be written as a sum of four squares. Can the same be
said of the set of $\{a^2 \mid a \text{ is any integer not equal to } 7\}$? If this could be
proved, it would only remain to check if all the numbers up to $599$ can be written as the sum
of $4$ squares none of which is $7^2$."
- _David S. Newman_, May 02 2014

Note that $0 \in \mathbb{N} \setminus \{7\}$ allows representations as a sum of at most four
positive squares none of which is $7^2$.

Answered affirmatively by W. Chae, Y.-S. Ji, K. Kim, K. Kim, B.-K. Oh and J. Yoon,
*Sums of squares of integers except for a fixed one*,
[arXiv:2504.03467](https://arxiv.org/abs/2504.03467): their main theorem gives $M(7) = 4$,
i.e. every positive integer is a sum of at most four squares of nonnegative integers
different from $7$.
-/
@[category research solved, question, AMS 11]
theorem conjecture_2 :
    ∀ n : ℕ, ∃ a b c d : ℕ,
      a ≠ 7 ∧ b ≠ 7 ∧ c ≠ 7 ∧ d ≠ 7 ∧ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by
  sorry

end OeisA241898
