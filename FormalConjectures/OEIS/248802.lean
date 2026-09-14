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
# Smallest prime factors of $2^{2^n+2} + 3$

Smallest prime factor of $2^{2^n+2} + 3$.

*References:*
- [A248802](https://oeis.org/A248802)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA248802


/--
Smallest prime factor of $2^{2^n+2} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def CoveredByC1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0,
and m is not 1 mod 5, predicting a(k)=271. -/
def CoveredByC2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0,
and m is not 0 mod 5, predicting a(k)=523. -/
def CoveredByC3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0


@[category test, AMS 11]
lemma a_0 : a 0 = 11 := by native_decide

@[category test, AMS 11]
lemma a_1 : a 1 = 19 := by native_decide

@[category test, AMS 11]
lemma a_2 : a 2 = 67 := by native_decide

@[category test, AMS 11]
lemma a_3 : a 3 = 13 := by native_decide

@[category test, AMS 11]
lemma a_4 : a 4 = 262147 := by native_decide


/--
Conjecture 1: $a(10n+2) = 67$ for $n \ge 0$. - _Chai Wah Wu_, Oct 21 2019

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/248802.wip.lean#L208"]
theorem a_ten_mul_add_two_eq (n : ℕ) : a (10 * n + 2) = 67 := by
    sorry


/--
Conjecture 4: $a(58n+26) = 1399$ for $n \ge 0$ and when it is not covered by Conjectures 1-3. - _Chai Wah Wu_, Oct 21 2019

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/248802.wip.lean#L982"]
theorem a_fifty_eight_mul_add_twenty_six_eq (n : ℕ) :
    (¬CoveredByC1 (58 * n + 26) ∧ ¬CoveredByC2 (58 * n + 26) ∧
    ¬CoveredByC3 (58 * n + 26)) → a (58 * n + 26) = 1399 := by
    sorry

end OeisA248802
