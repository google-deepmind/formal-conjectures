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
# A103311: A transform of the Fibonacci numbers.

The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
Conjecture: all elements in absolute value are Fibonacci numbers.

*References:*
- [A103311](https://oeis.org/A103311)
- [Advancing Mathematics Research with AI-Driven Formal Proof Search](https://arxiv.org/abs/2605.22763) by *George Tsoukalas et al.*, arXiv:2605.22763 [cs.AI] (2026)
-/

namespace OeisA103311

/-- The primary defining sequence `a`.
$a(n)$ is a transform of the Fibonacci numbers satisfying the linear recurrence relation:
$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$. -/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n

/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
lemma test_a_0 : a 0 = 0 := by decide

@[category test, AMS 11]
lemma test_a_1 : a 1 = 1 := by decide

@[category test, AMS 11]
lemma test_a_2 : a 2 = 1 := by decide

@[category test, AMS 11]
lemma test_a_3 : a 3 = 0 := by decide

@[category test, AMS 11]
lemma test_a_4 : a 4 = -2 := by decide

/--
Conjecture: all elements in absolute value are Fibonacci numbers.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using lean4 at "https://github.com/google-deepmind/alphaproof-nexus-results/blob/main/APNOutputs/OEIS/oeis_103311_conjecture_0.lean"]
theorem main_conjecture (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
  sorry

end OeisA103311
