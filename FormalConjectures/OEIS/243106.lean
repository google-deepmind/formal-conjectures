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
# Signed digit sums in bases $b \ge 5$

The sequence is defined by
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.

Generalizing the digit pattern observed in $a(n)$, it was conjectured on the OEIS entry that
for any base $b \ge 5$ and any choice of signs $\pm 1$, the absolute value of $\sum_{k=1}^n \pm b^k$
only contains digits in $\{0, 1, b-2, b-1\}$.

*References:*
- [A243106](https://oeis.org/A243106)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA243106


open Finset

/--
The sequence
$$a(n) = \sum_{k=1}^n (-1)^{\operatorname{isprime}(k)} 10^k$$
where the sign is $-1$ if $k$ is prime, and $1$ if $k$ is not prime.
-/
def a (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k


@[category test, AMS 11]
lemma a_1 : a 1 = 10 := by rfl

@[category test, AMS 11]
lemma a_2 : a 2 = -90 := by rfl

@[category test, AMS 11]
lemma a_3 : a 3 = -1090 := by rfl

@[category test, AMS 11]
lemma a_4 : a 4 = 8910 := by rfl

@[category test, AMS 11]
lemma a_5 : a 5 = -91090 := by rfl


/--
Conjecture: When expressed in base $b \ge 5$, the absolute value of any partial sum $\sum \pm b^k$ only contains digits belonging to $\{0, 1, b-2, b-1\}$.

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/243106.wip.lean#L140"]
theorem digits_sum_restricted (b n : ℕ) (hb : b ≥ 5) :
    ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
      let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
      ∀ d ∈ (b.digits x.natAbs), d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
    sorry

end OeisA243106
