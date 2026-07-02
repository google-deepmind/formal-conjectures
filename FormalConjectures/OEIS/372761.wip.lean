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
# Conjectures associated with A372761

Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.

The total value of the continued fraction $C_n$.

*References:*
- [A372761](https://oeis.org/A372761)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

namespace OeisA372761


open scoped Nat

open Rat

/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.
-/
noncomputable def continued_fraction_tail (n : ℕ) : ℕ → ℚ
| k =>
  if n ≥ 4 then
    if k = n - 1 then
      (n - 1 : ℚ) - (n : ℚ) / (n + 4 : ℚ)
    else if 3 ≤ k ∧ k < n - 1 then
      let k_succ_val := continued_fraction_tail n (k + 1)
      -- Division by zero handling for total function definition
      if k_succ_val = 0 then 0 else
        (k : ℚ) - (k + 1 : ℚ) / k_succ_val
    else
      0
  else
    0
termination_by k => n - k

/--
The total value of the continued fraction $C_n$.
-/
noncomputable def continued_fraction_val (n : ℕ) : ℚ :=
  if n ≤ 2 then
    0
  else if n = 3 then
    -- Formula for n=3: 1 / (2 - 3 / (3 + 4)) = 7/11
    let val : ℚ := 2 - 3 / 7
    if val = 0 then 0 else 1 / val
  else -- n ≥ 4
    let A3 := continued_fraction_tail n 3
    let val : ℚ := 2 - 3 / A3

    -- Division by zero check for the final rational value
    if val = 0 then 0 else 1 / val

/--
A372761: Denominator of the continued fraction
$$ \frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{n+4}}}}}} $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  if n < 3 then 0 -- Sequence starts at n=3.
  else (continued_fraction_val n).den


@[category test, AMS 11]
lemma a_four : a 4 = 4 := by
  delta a continued_fraction_val; repeat rw [continued_fraction_tail]; norm_num

@[category test, AMS 11]
lemma a_five : a 5 = 7 := by
  delta a continued_fraction_val; repeat rw [continued_fraction_tail]; norm_num

@[category test, AMS 11]
lemma a_six : a 6 = 13 := by
  delta a continued_fraction_val; repeat rw [continued_fraction_tail]; norm_num

@[category test, AMS 11]
lemma a_seven : a 7 = 31 := by
  delta a continued_fraction_val; repeat rw [continued_fraction_tail]; norm_num


/--
Recursive function to compute $A_k(n)$, the denominator tail $k - \frac{k+1}{A_{k+1}(n)}$.
The base case is at $k = n - 1$, where $A_{n-1} = (n-1) - \frac{n}{n+4}$.

The total value of the continued fraction $C_n$.

A formal proof has been found with the methods described in [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/mo271/formal-conjectures/blob/a32396489dcb8f86c3549b93aa358ac6a10a3a1f/FormalConjectures/OEIS/372761.wip.lean#L733"]
theorem target_theorem_0
  : ∀ p : ℕ, Nat.Prime p ∧ p % 2 = 1 ∧ p ≠ 3 ∧ p ≠ 5 → ∃! n, n ≥ 3 ∧ a n = p := by
    sorry

end OeisA372761
