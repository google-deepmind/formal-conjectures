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
# Fibonacci transform satisfying $|a(n)| = F(n+1)$

The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.

*References:*
- [A103311](https://oeis.org/A103311)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA103311


/--
The sequence $a(n)$ satisfies the linear recurrence relation:
$$a(n) = 3a(n-1) - 4a(n-2) + 2a(n-3) - a(n-4)$$
with initial terms $a(0)=0, a(1)=1, a(2)=1, a(3)=0$.
The sequence takes values in $\mathbb{Z}$.
-/
def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| 2 => 1
| 3 => 0
| n + 4 => 3 * a (n + 3) - 4 * a (n + 2) + 2 * a (n + 1) - a n


@[category test, AMS 11]
lemma a_0 : a 0 = 0 := by rfl

@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 0 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = -2 := by rfl


/--
Fibonacci transform satisfying $|a(n)| = F(n+1)$.

Conjecture: all elements in absolute value are Fibonacci numbers.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/103311.wip.lean#L218"]
theorem a_abs_eq_fib (n : ℕ) : ∃ m : ℕ, Int.natAbs (a n) = Nat.fib m := by
    sorry

end OeisA103311
