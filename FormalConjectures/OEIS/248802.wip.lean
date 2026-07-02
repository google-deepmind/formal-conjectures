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
# Conjectures associated with A248802

A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.

An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67.

*References:*
- [A248802](https://oeis.org/A248802)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA248802


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.
-/
def a (n : ℕ) : ℕ := (2 ^ (2 ^ n + 2) + 3).minFac

/-- An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67. -/
def covered_by_C1 (k : ℕ) : Prop := ∃ m : ℕ, k = 10 * m + 2

/-- An index k is covered by Conjecture 2 if k = 36m + 16 for some m >= 0,
and m is not 1 mod 5, predicting a(k)=271. -/
def covered_by_C2 (k : ℕ) : Prop := ∃ m : ℕ, k = 36 * m + 16 ∧ m % 5 ≠ 1

/-- An index k is covered by Conjecture 3 if k = 84m + 22 for some m >= 0,
and m is not 0 mod 5, predicting a(k)=523. -/
def covered_by_C3 (k : ℕ) : Prop := ∃ m : ℕ, k = 84 * m + 22 ∧ m % 5 ≠ 0


@[category test, AMS 11]
lemma a_zero : a 0 = 11 := by native_decide

@[category test, AMS 11]
lemma a_one : a 1 = 19 := by native_decide

@[category test, AMS 11]
lemma a_two : a 2 = 67 := by native_decide

@[category test, AMS 11]
lemma a_three : a 3 = 13 := by native_decide

@[category test, AMS 11]
lemma a_four : a 4 = 262147 := by native_decide


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.

An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/248802.wip.lean#L208"]
theorem target_theorem_0
  (n : ℕ) : a (10 * n + 2) = 67 := by
    sorry


/--
A248802: Smallest prime factor of $2^{(2^n+2)} + 3$.

An index k is covered by Conjecture 1 if k = 10m + 2 for some m >= 0, predicting a(k)=67.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/248802.wip.lean#L982"]
theorem target_theorem_4
  (n : ℕ) : (¬covered_by_C1 (58 * n + 26) ∧ ¬covered_by_C2 (58 * n + 26) ∧
    ¬covered_by_C3 (58 * n + 26)) → a (58 * n + 26) = 1399 := by
    sorry

end OeisA248802
