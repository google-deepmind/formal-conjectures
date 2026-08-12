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
# Primality and primitive root property from divisibility $n \mid (a(n-1) + 2^{n-2})$

$a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it
as a function $\mathbb{N} \to \mathbb{N}$.

*References:*
- [A091669](https://oeis.org/A091669)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA91669


open Nat BigOperators

/--
$a(n) = \frac{2^{n-1}}{n!} \prod_{k=1}^{n-1} (2^k-1)$.
The sequence $a(n)$ is composed of natural numbers, thus we define it
as a function $\mathbb{N} \to \mathbb{N}$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 -- Sequence is defined for n >= 1.
  else
    let n_pred : ℕ := n.pred

    -- The numerator of the expression. Both factors are in ℕ.
    let numerator : ℕ := (2 ^ n_pred) * (Finset.Ico 1 n).prod (fun k => 2 ^ k - 1)

    -- The denominator is $n!$.
    let denominator : ℕ := n.factorial

    -- The division is exact, since the result is an integer sequence.
    numerator / denominator


@[category test, AMS 11]
lemma a_1 : a 1 = 1 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = 1 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = 2 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 7 := by rfl

@[category test, AMS 11]
lemma a_5 : a 5 = 42 := by rfl


/--
Conjecture (for $n > 2$): if $n \mid a(n-1) + 2^{n-2}$, then $n$ is a prime with primitive root 2 (A001122). - _Amiram Eldar_ and _Thomas Ordowski_, Jan 19 2020

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/91669.wip.lean#L250"]
theorem prime_and_primitive_root_of_dvd (n : ℕ) (hn : n > 2) : n ∣ (a (n - 1) + 2 ^ (n - 2)) →
    Nat.Prime n ∧ IsPrimitiveRoot (2 : ZMod n) (Nat.totient n) := by
    sorry

end OeisA91669
