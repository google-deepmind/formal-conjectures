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
# Conjectures associated with A113254

A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation
$a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.

*References:*
- [A113254](https://oeis.org/A113254)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA113254


open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation
$a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'


@[category test, AMS 11]
lemma a_zero : a 0 = -1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 4 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 176 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 3136 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = -15616 := by rfl


/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation
$a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/113254.wip.lean#L130"]
theorem a_odd_is_square : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
    sorry

end OeisA113254
