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
# Conjectures associated with a

a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling
the subtraction via `Nat.pred`.

*References:*
- [A278070](https://oeis.org/A278070)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA278070


open Nat Finset

/--
a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling
the subtraction via `Nat.pred`.
-/
def a (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).sum fun k =>
    (n.choose k) * ((n + k).pred.choose k) * (k.factorial)


@[category test, AMS 11]
lemma a_zero : a 0 = 1 := by rfl

@[category test, AMS 11]
lemma a_one : a 1 = 2 := by rfl

@[category test, AMS 11]
lemma a_two : a 2 = 11 := by rfl

@[category test, AMS 11]
lemma a_three : a 3 = 106 := by rfl

@[category test, AMS 11]
lemma a_four : a 4 = 1457 := by rfl


/--
a: $a(n) = \text{hypergeometric}([n, -n], [], -1)$.
This is equivalent to the combinatorial sum:
$$a(n) = \sum_{k=0}^n \binom{n}{k} \binom{n+k-1}{k} k!$$
The expression uses $\mathbb{N}$ arithmetic throughout, safely handling
the subtraction via `Nat.pred`.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/278070.wip.lean#L68"]
theorem target_theorem_0
  : ∀ (n k : ℕ), Nat.ModEq k (a (n + k)) (a n) := by
    sorry

end OeisA278070
