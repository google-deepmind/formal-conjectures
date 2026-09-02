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
# Unique realization of odd primes $p \notin \{3, 5\}$ by continued fraction values

$a(n)$ is the denominator of the finite continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}}$$

*References:*
- [A372761](https://oeis.org/A372761)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA372761


open scoped Nat

open Rat

/--
Recursive helper computing the continued fraction denominator $R_k(n)$ for $2 \le k \le n-1$,
where $R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$ with base case $R_{n-1}(n) = (n-1) - \frac{n}{n+4}$.
-/
def continuedFractionDenominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    if 2 ≤ k ∧ k ≤ n - 1 then
      if k = n - 1 then
        (k : ℚ) - (n : ℚ) / (n + 4 : ℚ)
      else
        let R_next := continuedFractionDenominator n (k + 1)
        if R_next = 0 then 0 else (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (1 / continuedFractionDenominator n 2).den


@[category test, AMS 11]
lemma a_3 : a 3 = 11 := by
  delta a; repeat rw [continuedFractionDenominator]; norm_num

@[category test, AMS 11]
lemma a_4 : a 4 = 4 := by
  delta a; repeat rw [continuedFractionDenominator]; norm_num

@[category test, AMS 11]
lemma a_5 : a 5 = 7 := by
  delta a; repeat rw [continuedFractionDenominator]; norm_num

@[category test, AMS 11]
lemma a_6 : a 6 = 13 := by
  delta a; repeat rw [continuedFractionDenominator]; norm_num

@[category test, AMS 11]
lemma a_7 : a 7 = 31 := by
  delta a; repeat rw [continuedFractionDenominator]; norm_num


/--
Conjecture: Except for 3 and 5, all odd primes appear in the sequence once. - _Thomas Scheuerle_, May 11 2024

A formal proof has been found with the methods described in
[arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using lean4 at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/372761.wip.lean#L733"]
theorem exists_unique_a_eq_prime :
    ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 → ∃! n, n ≥ 3 ∧ a n = p := by
    sorry

end OeisA372761
